import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S5_209
import SemigroupBasis.Subdirect

/-!
# The recorded `S2_4` / `S5_209` ten-law candidate

This module records the exact candidate with SHA-256
`2412548b6e9e9d7d4123547fb2764ca3e4858c49a26429e3d45a66b1960731ec`.
It is shared by the six order-six roots
`S6_5613`, `S6_5621`, `S6_5659`, `S6_5668`, `S6_9450`, and `S6_9466`.

The two finite-model checks below establish soundness only. Completeness of
this exact candidate is addressed separately in
`Order6FactorPairS2_4S5_209Obstruction`.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def xxx : Word Nat := w 0 [0, 0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xxyx : Word Nat := w 0 [0, 1, 0]
def xyxx : Word Nat := w 0 [1, 0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xyyx : Word Nat := w 0 [1, 1, 0]
def xxyyy : Word Nat := w 0 [0, 1, 1, 1]
def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
def xxyz : Word Nat := w 0 [0, 1, 2]
def xyxz : Word Nat := w 0 [1, 0, 2]
def xxyzy : Word Nat := w 0 [0, 1, 2, 1]
def xyyzx : Word Nat := w 0 [1, 1, 2, 0]
def xyzx : Word Nat := w 0 [1, 2, 0]
def xzyx : Word Nat := w 0 [2, 1, 0]
def xyzy : Word Nat := w 0 [1, 2, 1]
def xzyy : Word Nat := w 0 [2, 1, 1]

def powerLaw : Identity Nat := Identity.mk xxx xxxx
def initialContractionLaw : Identity Nat := Identity.mk xxxyx xxyx
def initialRotationLaw : Identity Nat := Identity.mk xxyx xyxx
def squareInterleaveLaw : Identity Nat := Identity.mk xxyy xyxy
def squareGatherLaw : Identity Nat := Identity.mk xxyy xyyx
def cubeEndpointLaw : Identity Nat := Identity.mk xxyyy xyyyx
def guardedGatherLaw : Identity Nat := Identity.mk xxyz xyxz
def guardedSquareRotationLaw : Identity Nat := Identity.mk xxyzy xyyzx
def closedInteriorSwapLaw : Identity Nat := Identity.mk xyzx xzyx
def repeatedFinalSwapLaw : Identity Nat := Identity.mk xyzy xzyy

/-- The exact ten laws in packet order. -/
def basis : List (Identity Nat) :=
  [ powerLaw,
    initialContractionLaw,
    initialRotationLaw,
    squareInterleaveLaw,
    squareGatherLaw,
    cubeEndpointLaw,
    guardedGatherLaw,
    guardedSquareRotationLaw,
    closedInteriorSwapLaw,
    repeatedFinalSwapLaw ]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

/-- Every recorded law preserves the literal first letter, hence is valid in
the two-element left-zero factor. -/
theorem modelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_4.table (by decide)

/-- Every recorded law is valid in the stored `S5_209` factor. -/
theorem modelsS5_209 :
    Models SemigroupBasis.Generated.S5_209.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S5_209.table (by decide)

end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal

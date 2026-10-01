import SemigroupBasis.BlockTraceDerives
import SemigroupBasis.FiniteReflection

namespace SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints

open SemigroupBasis
open SemigroupBasis.BlockTrace
open SemigroupBasis.CoRoots.S5_107

universe u

/-! ## Shared endpoint adapter -/

/-- Source-only interface between the shared block-trace theorem and a concrete
order-six root. The remaining family proof must supply normalization of every
nonempty word and show that target-valid identities preserve the retained-state
map and every dependent block order. -/
structure TraceCertificate {S : Type u}
    (candidate : Semigroup S) (basis : List (Identity Nat)) where
  commutes : Nat → Nat → Prop
  normalWord : Word Nat → Word Nat
  normalBlocks : Word Nat → List RetainedBlock
  renderNormal : ∀ word,
    renderRetainedBlocks (normalBlocks word) = (normalWord word).toList
  labelsNodup : ∀ word, RetainedLabelsNodup (normalBlocks word)
  derivesNormal : ∀ word, Derives basis word (normalWord word)
  sameStateMap : ∀ identity : Identity Nat,
    identity.SatisfiedBy candidate →
      SameRetainedStateMap
        (normalBlocks identity.lhs) (normalBlocks identity.rhs)
  dependentOrder : ∀ identity : Identity Nat,
    identity.SatisfiedBy candidate →
      SameDependentOrder commutes
        (normalBlocks identity.lhs) (normalBlocks identity.rhs)
  adjacentSwap : AdjacentSwapDerivable basis commutes

private theorem listDerives_toWords
    {basis : List (Identity Nat)} {left right : Word Nat}
    (derivation : ListDerives basis left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact derivation.toWord

/-- Convert the table model check and the family trace certificate into the
actual `BasisFor` endpoint. The middle derivation is exactly the reusable
`BlockTrace.blockTraceDerives` theorem. -/
theorem TraceCertificate.toBasisFor
    {S : Type u} {candidate : Semigroup S}
    {basis : List (Identity Nat)}
    (certificate : TraceCertificate candidate basis)
    (models : Models candidate basis) :
    BasisFor candidate basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  have middleList :
      ListDerives basis
        (renderRetainedBlocks (certificate.normalBlocks identity.lhs))
        (renderRetainedBlocks (certificate.normalBlocks identity.rhs)) :=
    SemigroupBasis.BlockTrace.blockTraceDerives
      (certificate.labelsNodup identity.lhs)
      (certificate.labelsNodup identity.rhs)
      (certificate.sameStateMap identity valid)
      (certificate.dependentOrder identity valid)
      certificate.adjacentSwap
  rw [certificate.renderNormal identity.lhs,
    certificate.renderNormal identity.rhs] at middleList
  exact (certificate.derivesNormal identity.lhs).trans <|
    (listDerives_toWords middleList).trans
      (certificate.derivesNormal identity.rhs).symm

/-! ## The three recorded representative-oriented basis families -/

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def lawXX_XXXX : Identity Nat :=
  ⟨w 0 [0], w 0 [0, 0, 0]⟩

def lawXXX_XXXX : Identity Nat :=
  ⟨w 0 [0, 0], w 0 [0, 0, 0]⟩

def lawXXXYYY_YYYXXX : Identity Nat :=
  ⟨w 0 [0, 0, 1, 1, 1], w 1 [1, 1, 0, 0, 0]⟩

def lawXXY_XYX : Identity Nat :=
  ⟨w 0 [0, 1], w 0 [1, 0]⟩

def lawXXYY_YYXX : Identity Nat :=
  ⟨w 0 [0, 1, 1], w 1 [1, 0, 0]⟩

def lawXXYYY_YYYXX : Identity Nat :=
  ⟨w 0 [0, 1, 1, 1], w 1 [1, 1, 0, 0]⟩

def lawXYY_YYX : Identity Nat :=
  ⟨w 0 [1, 1], w 1 [1, 0]⟩

def lawXYYY_YYYX : Identity Nat :=
  ⟨w 0 [1, 1, 1], w 1 [1, 1, 0]⟩

def lawXYX_YXX : Identity Nat :=
  ⟨w 0 [1, 0], w 1 [0, 0]⟩

/-- Recorded basis for bounded class 54. -/
def class54Basis : List (Identity Nat) :=
  [lawXX_XXXX, lawXXXYYY_YYYXXX, lawXXY_XYX, lawXXYY_YYXX,
    lawXXYYY_YYYXX, lawXYY_YYX, lawXYYY_YYYX]

/-- Recorded basis for bounded class 236. -/
def class236Basis : List (Identity Nat) :=
  [lawXXX_XXXX, lawXXXYYY_YYYXXX, lawXXYY_YYXX,
    lawXXYYY_YYYXX, lawXYX_YXX]

/-- Recorded basis for bounded class 389. -/
def class389Basis : List (Identity Nat) :=
  [lawXXX_XXXX, lawXXXYYY_YYYXXX, lawXXY_XYX,
    lawXXYY_YYXX, lawXXYYY_YYYXX]

/-! ## Finite model checks -/

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def finiteBasis (basis : List (Identity Nat)) :
    List (Identity (Fin 2)) :=
  basis.map fun identity => identity.map toFinTwo

private theorem models_of_finite_checks
    (candidate : FiniteTable) (basis : List (Identity Nat))
    (roundTrip : basis.all (fun identity =>
      decide ((identity.map toFinTwo).map Fin.val = identity)) = true)
    (checked : (finiteBasis basis).all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinTwo ∈ finiteBasis basis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinTwo).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp roundTrip) identity member
  rw [restored] at finiteValid
  exact finiteValid

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-! ## Exact catalogue roots and conditional endpoints -/

namespace S6_1262

/-- Exact one-based catalogue table:
`[[1,1,1,1,5,1],[1,1,1,1,5,2],[1,1,1,1,5,3],
  [1,1,2,1,5,4],[5,5,5,5,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 4 0 b else
    if a = 1 then row6 0 0 0 0 4 1 b else
      if a = 2 then row6 0 0 0 0 4 2 b else
        if a = 3 then row6 0 0 1 0 4 3 b else
          if a = 4 then row6 4 4 4 4 0 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bf07dec4b1b3646b98360c21c91f4f0fd774de5bc81d4783274119e985b03e5b"

abbrev basis : List (Identity Nat) := class54Basis
abbrev semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models semigroup basis :=
  models_of_finite_checks table basis (by decide) (by decide)

theorem basisFor (certificate : TraceCertificate semigroup basis) :
    BasisFor semigroup basis :=
  certificate.toBasisFor models

end S6_1262

namespace S6_1348

/-- Exact one-based catalogue table:
`[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],
  [3,3,1,1,1,4],[3,3,1,2,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 2 2 2 0 b else
    if a = 1 then row6 0 0 2 2 2 1 b else
      if a = 2 then row6 2 2 0 0 0 2 b else
        if a = 3 then row6 2 2 0 0 0 3 b else
          if a = 4 then row6 2 2 0 1 0 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c553a95215af6b38319e3cf84c66d6f25d8468daf5e8e3f36cbbfcacd1ceec59"

abbrev basis : List (Identity Nat) := class54Basis
abbrev semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models semigroup basis :=
  models_of_finite_checks table basis (by decide) (by decide)

theorem basisFor (certificate : TraceCertificate semigroup basis) :
    BasisFor semigroup basis :=
  certificate.toBasisFor models

end S6_1348

namespace S6_1354

/-- Exact one-based catalogue table:
`[[1,1,3,3,3,1],[1,1,3,3,3,2],[3,3,1,1,1,3],
  [3,3,1,1,1,4],[3,4,1,1,1,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 2 2 2 0 b else
    if a = 1 then row6 0 0 2 2 2 1 b else
      if a = 2 then row6 2 2 0 0 0 2 b else
        if a = 3 then row6 2 2 0 0 0 3 b else
          if a = 4 then row6 2 3 0 0 0 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ce9e238bcef502fae0ac867c590384f2afb18ec691a31ce5506efd1ed448902f"

abbrev basis : List (Identity Nat) := class54Basis
abbrev semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models semigroup basis :=
  models_of_finite_checks table basis (by decide) (by decide)

theorem basisFor (certificate : TraceCertificate semigroup basis) :
    BasisFor semigroup basis :=
  certificate.toBasisFor models

end S6_1354

namespace S6_3051

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,1,1,3,3],
  [1,1,2,1,4,4],[1,2,3,4,5,6],[1,2,3,4,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 1 1 b else
      if a = 2 then row6 0 0 0 0 2 2 b else
        if a = 3 then row6 0 0 1 0 3 3 b else
          if a = 4 then row6 0 1 2 3 4 5 b else
            row6 0 1 2 3 5 4 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cada8b454bab311f43b6ae505df3378f77b4e639d564a40114124d95bed4392f"

abbrev basis : List (Identity Nat) := class54Basis
abbrev semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models semigroup basis :=
  models_of_finite_checks table basis (by decide) (by decide)

theorem basisFor (certificate : TraceCertificate semigroup basis) :
    BasisFor semigroup basis :=
  certificate.toBasisFor models

end S6_3051

namespace S6_5627

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,3],
  [1,1,1,2,1,4],[1,1,3,1,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 0 1 b else
      if a = 2 then row6 0 0 0 0 0 2 b else
        if a = 3 then row6 0 0 0 1 0 3 b else
          if a = 4 then row6 0 0 2 0 4 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "36eb9dca2a96c3a027fc512ce5fbb180a4b2b5171882361914395857f2945d74"

abbrev basis : List (Identity Nat) := class236Basis
abbrev semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models semigroup basis :=
  models_of_finite_checks table basis (by decide) (by decide)

theorem basisFor (certificate : TraceCertificate semigroup basis) :
    BasisFor semigroup basis :=
  certificate.toBasisFor models

end S6_5627

namespace S6_5671

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,1,1,2,3],
  [1,1,1,2,4,4],[1,2,3,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 1 1 b else
      if a = 2 then row6 0 0 0 0 1 2 b else
        if a = 3 then row6 0 0 0 1 3 3 b else
          if a = 4 then row6 0 1 2 3 4 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "153143e7f99a4ccf7f82ab74bd17fe6347ba3afe17f9ee70ff131971424a334f"

abbrev basis : List (Identity Nat) := class236Basis
abbrev semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models semigroup basis :=
  models_of_finite_checks table basis (by decide) (by decide)

theorem basisFor (certificate : TraceCertificate semigroup basis) :
    BasisFor semigroup basis :=
  certificate.toBasisFor models

end S6_5671

namespace S6_9469

/-- Exact one-based catalogue table:
`[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,2,2,3,3],
  [1,1,2,2,3,4],[1,2,3,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 0 0 0 b else
    if a = 1 then row6 0 0 0 0 1 1 b else
      if a = 2 then row6 0 0 1 1 2 2 b else
        if a = 3 then row6 0 0 1 1 2 3 b else
          if a = 4 then row6 0 1 2 3 4 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2be98f17a452926ca75001e707b993d35a6ff2f8947eb3e8cc0a7c3af55302ea"

abbrev basis : List (Identity Nat) := class236Basis
abbrev semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models semigroup basis :=
  models_of_finite_checks table basis (by decide) (by decide)

theorem basisFor (certificate : TraceCertificate semigroup basis) :
    BasisFor semigroup basis :=
  certificate.toBasisFor models

end S6_9469

namespace S6_9624

/-- Exact one-based catalogue table:
`[[1,1,1,4,4,1],[1,1,1,4,4,2],[1,1,2,4,4,3],
  [4,4,4,4,4,4],[5,5,5,4,4,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then row6 0 0 0 3 3 0 b else
    if a = 1 then row6 0 0 0 3 3 1 b else
      if a = 2 then row6 0 0 1 3 3 2 b else
        if a = 3 then row6 3 3 3 3 3 3 b else
          if a = 4 then row6 4 4 4 3 3 4 b else
            row6 0 1 2 3 4 5 b

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "998265d97d6c0fec21262c7b219d162633389227ead22e46f8c65fa3b6cdddd3"

abbrev basis : List (Identity Nat) := class389Basis
abbrev semigroup : Semigroup (Fin 6) := table.semigroup

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models semigroup basis :=
  models_of_finite_checks table basis (by decide) (by decide)

theorem basisFor (certificate : TraceCertificate semigroup basis) :
    BasisFor semigroup basis :=
  certificate.toBasisFor models

end S6_9624

end SemigroupBasis.CoRoots.Order6BlockTraceRootEndpoints

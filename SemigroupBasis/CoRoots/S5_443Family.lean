import SemigroupBasis.CoRoots.S5_443CanonicalSemantics
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_443Family

open SemigroupBasis
open SemigroupBasis.Examples
open CanonicalSyntax
open CanonicalSemantics
open S5_614Semantics

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xyx : Word Nat := w 0 [1, 0]
def yxx : Word Nat := w 1 [0, 0]
def xxyy : Word Nat := w 0 [0, 1, 1]
def yyxx : Word Nat := w 1 [1, 0, 0]

def powerLaw : Identity Nat := ⟨xx, xxxx⟩
def gatherLaw : Identity Nat := ⟨xyx, yxx⟩
def squareCommutationLaw : Identity Nat := ⟨xxyy, yyxx⟩

/-- Edmunds' common exact basis for the `S5_443` family:
`xx = xxxx`, `xyx = yxx`, and `xxyy = yyxx`. -/
def basis : List (Identity Nat) :=
  [powerLaw, gatherLaw, squareCommutationLaw]

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def finiteBasis : List (Identity (Fin 2)) :=
  basis.map fun e => e.map toFinTwo

private theorem basis_roundTrip_checked :
    basis.all (fun e =>
      decide ((e.map toFinTwo).map Fin.val = e)) = true := by
  decide

private theorem basis_roundTrip
    (e : Identity Nat) (member : e ∈ basis) :
    (e.map toFinTwo).map Fin.val = e := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) e member

private theorem models_of_finite_checks
    (T : FiniteTable)
    (checked : finiteBasis.all T.checkIdentity = true) :
    Models T.semigroup basis := by
  intro e member
  have finiteMember : e.map toFinTwo ∈ finiteBasis :=
    List.mem_map.mpr ⟨e, member, rfl⟩
  have finiteValid :=
    T.checkIdentityNat_sound (e.map toFinTwo)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip e member] at finiteValid
  exact finiteValid

namespace S5_614

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_614.table.semigroup basis :=
  models_of_finite_checks Generated.Catalogue.S5_614.table (by decide)

theorem opposite_models :
    Models Generated.Catalogue.S5_614.table.semigroup.opposite
      (reversedBasis basis) :=
  models.oppositeReversed

private theorem reversed_basis_eq_syntax :
    reversedBasis basis = edmundsPeriodTwoBlocksBasis := by
  decide

private theorem listDerives_sound
    {xs ys : List Nat}
    (derivation : EdmundsPeriodTwoBlocksListDerives xs ys)
    (valuation : Nat → Fin 5) :
    listEval valuation xs = listEval valuation ys := by
  cases derivation with
  | empty => rfl
  | words wordDerivation =>
      have sound :=
        wordDerivation.sound
          (by
            rw [← reversed_basis_eq_syntax]
            exact opposite_models)
          valuation
      rw [eval_eq_listEval, eval_eq_listEval] at sound
      exact sound

/-- Unrestricted completeness in the opposite, first-occurrence orientation.
Every word normalizes to 1/2/3 blocks. Repeated blocks sort within the runs
between singleton separators, and the exact table separates the resulting
canonical segmented forms. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_614.table.semigroup.opposite
      (reversedBasis basis) := by
  rw [reversed_basis_eq_syntax]
  refine ⟨?_, ?_⟩
  · rw [← reversed_basis_eq_syntax]
    exact opposite_models
  · intro e valid
    have lhsNormal := edmundsPeriodTwoBlocksDerivesNormal e.lhs
    have rhsNormal := edmundsPeriodTwoBlocksDerivesNormal e.rhs
    cases hl : edmundsPeriodTwoBlocksNormalList e.lhs.toList with
    | nil =>
        exact False.elim <|
          edmundsPeriodTwoBlocksNormalList_cons_ne_nil
            e.lhs.head e.lhs.tail (by
              simpa [Word.toList] using hl)
    | cons lx ltail =>
        cases hr : edmundsPeriodTwoBlocksNormalList e.rhs.toList with
        | nil =>
            exact False.elim <|
              edmundsPeriodTwoBlocksNormalList_cons_ne_nil
                e.rhs.head e.rhs.tail (by
                  simpa [Word.toList] using hr)
        | cons rx rtail =>
            rw [hl] at lhsNormal
            rw [hr] at rhsNormal
            let lhsList := lx :: ltail
            let rhsList := rx :: rtail
            let lhsSegments :=
              edmundsPeriodTwoCanonicalSegmentsOfNormalList lhsList
            let rhsSegments :=
              edmundsPeriodTwoCanonicalSegmentsOfNormalList rhsList
            have lhsForm : EdmundsPeriodTwoBlocksNormal lhsList := by
              simpa [lhsList, hl] using
                edmundsPeriodTwoBlocksNormalList_normal e.lhs.toList
            have rhsForm : EdmundsPeriodTwoBlocksNormal rhsList := by
              simpa [rhsList, hr] using
                edmundsPeriodTwoBlocksNormalList_normal e.rhs.toList
            have lhsCanonical : SegmentsCanonical lhsSegments := by
              simpa [lhsSegments] using
                edmundsPeriodTwoCanonicalSegments_canonical lhsForm
            have rhsCanonical : SegmentsCanonical rhsSegments := by
              simpa [rhsSegments] using
                edmundsPeriodTwoCanonicalSegments_canonical rhsForm
            have lhsCanonDerives :
                EdmundsPeriodTwoBlocksListDerives lhsList
                  (renderEdmundsPeriodTwoSegments lhsSegments) := by
              simpa [lhsSegments,
                edmundsPeriodTwoCanonicalRender] using
                  edmundsPeriodTwoCanonicalDerivation lhsForm
            have rhsCanonDerives :
                EdmundsPeriodTwoBlocksListDerives rhsList
                  (renderEdmundsPeriodTwoSegments rhsSegments) := by
              simpa [rhsSegments,
                edmundsPeriodTwoCanonicalRender] using
                  edmundsPeriodTwoCanonicalDerivation rhsForm
            have canonicalEvalEqual :
                ∀ valuation : Nat → Fin 5,
                  listEval valuation
                      (renderEdmundsPeriodTwoSegments lhsSegments) =
                    listEval valuation
                      (renderEdmundsPeriodTwoSegments rhsSegments) := by
              intro valuation
              have lhsNormalSound :=
                lhsNormal.sound
                  (by
                    rw [← reversed_basis_eq_syntax]
                    exact opposite_models)
                  valuation
              have rhsNormalSound :=
                rhsNormal.sound
                  (by
                    rw [← reversed_basis_eq_syntax]
                    exact opposite_models)
                  valuation
              have validSound := valid valuation
              rw [eval_eq_listEval, eval_eq_listEval] at lhsNormalSound rhsNormalSound
              rw [eval_eq_listEval, eval_eq_listEval] at validSound
              have lhsCanonSound :=
                listDerives_sound lhsCanonDerives valuation
              have rhsCanonSound :=
                listDerives_sound rhsCanonDerives valuation
              exact lhsCanonSound.symm.trans <|
                lhsNormalSound.symm.trans <|
                  validSound.trans <|
                    rhsNormalSound.trans rhsCanonSound
            have segmentsEqual :
                lhsSegments = rhsSegments :=
              canonical_segments_eq_of_eval_eq
                lhsCanonical rhsCanonical canonicalEvalEqual
            have renderedEqual :
                renderEdmundsPeriodTwoSegments lhsSegments =
                  renderEdmundsPeriodTwoSegments rhsSegments := by
              rw [segmentsEqual]
            have middle :
                EdmundsPeriodTwoBlocksListDerives
                  (renderEdmundsPeriodTwoSegments lhsSegments)
                  (renderEdmundsPeriodTwoSegments rhsSegments) := by
              rw [renderedEqual]
              exact EdmundsPeriodTwoBlocksListDerives.refl _
            have canonicalBridge :
                EdmundsPeriodTwoBlocksListDerives lhsList rhsList :=
              lhsCanonDerives.trans (middle.trans rhsCanonDerives.symm)
            have canonicalBridgeNonempty :
                EdmundsPeriodTwoBlocksListDerives
                  (lx :: ltail) (rx :: rtail) := by
              simpa [lhsList, rhsList] using canonicalBridge
            cases canonicalBridgeNonempty with
            | words bridge =>
                exact Derives.trans lhsNormal <|
                  Derives.trans bridge (Derives.symm rhsNormal)

/-- Completeness in the stored catalogue orientation. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_614.table.semigroup basis := by
  have reversed := opposite_basis_complete.oppositeReversed
  simpa using reversed

end S5_614

end SemigroupBasis.CoRoots.S5_443Family

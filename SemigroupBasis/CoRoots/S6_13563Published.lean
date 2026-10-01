import SemigroupBasis.CoRoots.Order6PublishedMonoid15Normalization

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid15.S6_13563

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6PublishedMonoid15

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact catalogue table for Lee--Li's monoid K, in the direct orientation:
`[[1,1,1,1,1,1],[1,1,1,1,2,3],[3,3,3,3,3,3],
  [1,2,3,4,4,3],[1,2,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 1 2 right else
      if left = 2 then row6 2 2 2 2 2 2 right else
        if left = 3 then row6 0 1 2 3 3 2 right else
          if left = 4 then row6 0 1 2 3 4 5 right else
            row6 5 5 5 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "095b7f57d0afc776d72892a7bd170df0ea356ed02c454705f760eb92b1e738b5"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 3],
        [3, 3, 3, 3, 3, 3], [1, 2, 3, 4, 4, 3],
        [1, 2, 3, 4, 5, 6], [6, 6, 6, 6, 6, 6]] := by
  decide

theorem identityElement_certificate :
    (∀ value : Fin 6, mul 4 value = value) ∧
      (∀ value : Fin 6, mul value 4 = value) := by
  decide

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-! ## The literal S5_870 submonoid -/

/-- The one-based inclusion `[1,2,3,5,6]`. -/
def s5_870Embedding :
    Embedding S5_870.table.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 6)
    else if value.val = 1 then (1 : Fin 6)
    else if value.val = 2 then (2 : Fin 6)
    else if value.val = 3 then (4 : Fin 6)
    else (5 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

def s5_870EmbeddingOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (s5_870Embedding.toFun value).val + 1

theorem s5_870EmbeddingOneBased_certificate :
    s5_870EmbeddingOneBased = [1, 2, 3, 5, 6] := by
  decide

theorem valid_gapSignature_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    S5_870.gapSignature identity.lhs =
      S5_870.gapSignature identity.rhs :=
  S5_870.valid_gapSignature_eq identity
    (s5_870Embedding.pullback_identity identity valid)

/-! ## Exact post-second marker semantics -/

private theorem decode_step
    (state : PostSecondState) (selected protector : Nat)
    (terminator : Option Nat) (letter : Nat) :
    mul state.decodeK (markerValuation selected protector terminator letter) =
      (state.step
        (markerLetter selected protector terminator letter)).decodeK := by
  unfold markerValuation
  cases markerLetter selected protector terminator letter <;>
    cases state <;> decide

private theorem decodeAlt_step
    (state : PostSecondState) (selected protector : Nat)
    (terminator : Option Nat) (letter : Nat) :
    mul state.decodeKAlt
        (markerValuationAlt selected protector terminator letter) =
      (state.step
        (markerLetter selected protector terminator letter)).decodeKAlt := by
  unfold markerValuationAlt
  cases markerLetter selected protector terminator letter <;>
    cases state <;> decide

private theorem fold_marker
    (selected protector : Nat) (terminator : Option Nat) :
    ∀ (letters : List Nat) (state : PostSecondState),
      letters.foldl
          (fun current letter =>
            mul current
              (markerValuation selected protector terminator letter))
          state.decodeK =
        (letters.foldl
          (fun current letter =>
            current.step
              (markerLetter selected protector terminator letter))
          state).decodeK
  | [], _ => rfl
  | letter :: rest, state => by
      simp only [List.foldl_cons]
      rw [decode_step]
      exact fold_marker selected protector terminator rest _

private theorem fold_marker_alt
    (selected protector : Nat) (terminator : Option Nat) :
    ∀ (letters : List Nat) (state : PostSecondState),
      letters.foldl
          (fun current letter =>
            mul current
              (markerValuationAlt selected protector terminator letter))
          state.decodeKAlt =
        (letters.foldl
          (fun current letter =>
            current.step
              (markerLetter selected protector terminator letter))
          state).decodeKAlt
  | [], _ => rfl
  | letter :: rest, state => by
      simp only [List.foldl_cons]
      rw [decodeAlt_step]
      exact fold_marker_alt selected protector terminator rest _

private def markerEvalList
    (selected protector : Nat) (terminator : Option Nat)
    (letters : List Nat) : Fin 6 :=
  letters.foldl
    (fun current letter =>
      mul current (markerValuation selected protector terminator letter)) 4

private def markerEvalAltList
    (selected protector : Nat) (terminator : Option Nat)
    (letters : List Nat) : Fin 6 :=
  letters.foldl
    (fun current letter =>
      mul current
        (markerValuationAlt selected protector terminator letter)) 4

private theorem markerEvalList_toList
    (word : Word Nat) (selected protector : Nat)
    (terminator : Option Nat) :
    markerEvalList selected protector terminator word.toList =
      table.semigroup.eval
        (markerValuation selected protector terminator) word := by
  cases word with
  | mk head tail =>
      simp only [markerEvalList, Word.toList, List.foldl_cons,
        Semigroup.eval]
      change
        tail.foldl
            (fun current letter =>
              mul current
                (markerValuation selected protector terminator letter))
            (mul 4 (markerValuation selected protector terminator head)) =
          tail.foldl
            (fun current letter =>
              mul current
                (markerValuation selected protector terminator letter))
            (markerValuation selected protector terminator head)
      have leftIdentity :
          mul 4 (markerValuation selected protector terminator head) =
            markerValuation selected protector terminator head := by
        unfold markerValuation
        cases markerLetter selected protector terminator head <;> decide
      rw [leftIdentity]

private theorem markerEvalAltList_toList
    (word : Word Nat) (selected protector : Nat)
    (terminator : Option Nat) :
    markerEvalAltList selected protector terminator word.toList =
      table.semigroup.eval
        (markerValuationAlt selected protector terminator) word := by
  cases word with
  | mk head tail =>
      simp only [markerEvalAltList, Word.toList, List.foldl_cons,
        Semigroup.eval]
      change
        tail.foldl
            (fun current letter =>
              mul current
                (markerValuationAlt selected protector terminator letter))
            (mul 4
              (markerValuationAlt selected protector terminator head)) =
          tail.foldl
            (fun current letter =>
              mul current
                (markerValuationAlt selected protector terminator letter))
            (markerValuationAlt selected protector terminator head)
      have leftIdentity :
          mul 4
              (markerValuationAlt selected protector terminator head) =
            markerValuationAlt selected protector terminator head := by
        unfold markerValuationAlt
        cases markerLetter selected protector terminator head <;> decide
      rw [leftIdentity]

theorem markerEval_eq_decode
    (word : Word Nat) (selected protector : Nat)
    (terminator : Option Nat) :
    table.semigroup.eval
        (markerValuation selected protector terminator) word =
      (postSecondState word selected protector terminator).decodeK := by
  rw [← markerEvalList_toList word selected protector terminator]
  exact fold_marker selected protector terminator word.toList .neutral

theorem markerEvalAlt_eq_decode
    (word : Word Nat) (selected protector : Nat)
    (terminator : Option Nat) :
    table.semigroup.eval
        (markerValuationAlt selected protector terminator) word =
      (postSecondState word selected protector terminator).decodeKAlt := by
  rw [← markerEvalAltList_toList word selected protector terminator]
  exact fold_marker_alt selected protector terminator word.toList .neutral

theorem valid_decodeK_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (selected protector : Nat) (terminator : Option Nat) :
    (postSecondState identity.lhs selected protector terminator).decodeK =
      (postSecondState identity.rhs selected protector terminator).decodeK := by
  rw [← markerEval_eq_decode, ← markerEval_eq_decode]
  exact valid (markerValuation selected protector terminator)

theorem valid_decodeKAlt_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (selected protector : Nat) (terminator : Option Nat) :
    (postSecondState identity.lhs selected protector terminator).decodeKAlt =
      (postSecondState identity.rhs selected protector terminator).decodeKAlt := by
  rw [← markerEvalAlt_eq_decode, ← markerEvalAlt_eq_decode]
  exact valid (markerValuationAlt selected protector terminator)

theorem valid_postSecondState_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    (selected protector : Nat) (terminator : Option Nat) :
    postSecondState identity.lhs selected protector terminator =
      postSecondState identity.rhs selected protector terminator :=
  PostSecondState.eq_of_decodeK_pair
    (valid_decodeK_eq identity valid selected protector terminator)
    (valid_decodeKAlt_eq identity valid selected protector terminator)

/-- The exact K table separates every component of the refined signature. -/
theorem valid_refinedGapSignature_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    refinedGapSignature identity.lhs =
      refinedGapSignature identity.rhs := by
  apply RefinedGapSignature.ext
  · exact valid_gapSignature_eq identity valid
  · funext selected protector terminator
    exact valid_postSecondState_eq identity valid
      selected protector terminator

/-- Unconditional direct basis endpoint for Lee--Li's monoid K. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_of_refinedGapSignature_eq
    (valid_refinedGapSignature_eq identity valid)

/-- Unconditional endpoint for the opposite of Lee--Li's monoid K. -/
theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basisFor.oppositeReversed

/-! ## The two invalid S5 cap laws, recorded as executable witnesses -/

private def localWord (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

def xxtxIdentity : Identity Nat :=
  ⟨localWord 0 [0, 3, 0], localWord 0 [0, 3]⟩

def xhxtxIdentity : Identity Nat :=
  ⟨localWord 0 [1, 0, 3, 0], localWord 0 [1, 0, 3]⟩

def invalidCapValuation : Nat → Fin 6 :=
  fun letter =>
    if letter = 0 then 3 else if letter = 3 then 1 else 4

theorem xxtxIdentity_fails :
    xxtxIdentity.FailsAt table.semigroup invalidCapValuation := by
  change
    table.semigroup.eval invalidCapValuation xxtxIdentity.lhs ≠
      table.semigroup.eval invalidCapValuation xxtxIdentity.rhs
  decide

theorem xhxtxIdentity_fails :
    xhxtxIdentity.FailsAt table.semigroup invalidCapValuation := by
  change
    table.semigroup.eval invalidCapValuation xhxtxIdentity.lhs ≠
      table.semigroup.eval invalidCapValuation xhxtxIdentity.rhs
  decide

theorem not_models_xxtxIdentity :
    ¬ xxtxIdentity.SatisfiedBy table.semigroup :=
  Identity.not_satisfiedBy_of_failsAt xxtxIdentity_fails

theorem not_models_xhxtxIdentity :
    ¬ xhxtxIdentity.SatisfiedBy table.semigroup :=
  Identity.not_satisfiedBy_of_failsAt xhxtxIdentity_fails

end SemigroupBasis.CoRoots.Order6PublishedMonoid15.S6_13563

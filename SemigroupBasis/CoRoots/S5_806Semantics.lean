import SemigroupBasis.CoRoots.S5_806Canonical
import SemigroupBasis.Examples.ConnectedComponentFourSemanticComplete
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_806

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Embedded S4_70 component detector -/

/-- The recorded copy `[1,2,4,5]` of `S4_70` inside `S5_806`. -/
def componentEmbedding :
    Embedding connectedComponentFour.semigroup
      Generated.Catalogue.S5_806.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩ else
      if value.val = 1 then ⟨1, by decide⟩ else
        if value.val = 2 then ⟨3, by decide⟩ else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem valid_s4_70 (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_806.table.semigroup) :
    identity.SatisfiedBy connectedComponentFour.semigroup :=
  componentEmbedding.pullback_identity identity valid

/-- The embedded factor determines every ordered component support and unary
repeat flag. -/
theorem valid_sameBaseComponentSignatures
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_806.table.semigroup) :
    connectedComponentSignaturesWord identity.lhs =
      connectedComponentSignaturesWord identity.rhs := by
  have rootValid := valid_s4_70 identity valid
  have lhsDerivation :=
    connectedComponentFour_derivesCanonical identity.lhs
  have rhsDerivation :=
    connectedComponentFour_derivesCanonical identity.rhs
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.lhs) =
          connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender identity.rhs) := by
    intro valuation
    have lhsSound :=
      lhsDerivation.sound connectedComponentFourBasis_models valuation
    have rhsSound :=
      rhsDerivation.sound connectedComponentFourBasis_models valuation
    exact lhsSound.symm.trans <| (rootValid valuation).trans rhsSound
  exact
    connectedComponentCanonical_eq_of_equalEval
      (connectedComponentFourSignaturesWord_canonical identity.lhs)
      (connectedComponentFourSignaturesWord_canonical identity.rhs)
      (connectedComponentCanonicalRender identity.lhs)
      (connectedComponentCanonicalRender identity.rhs)
      (connectedComponentCanonicalRender_toList identity.lhs)
      (connectedComponentCanonicalRender_toList identity.rhs)
      normalizedEval

/-! ## Explicit whole-word final-variable marker -/

private abbrev table := Generated.Catalogue.S5_806.table

def listStep : Option (Fin 5) → Fin 5 → Option (Fin 5)
  | none, next => some next
  | some current, next => some (table.mul current next)

def evalFrom
    {alpha : Type} (initial : Option (Fin 5))
    (valuation : alpha → Fin 5) (letters : List alpha) :
    Option (Fin 5) :=
  letters.foldl
    (fun current letter => listStep current (valuation letter)) initial

def evalList
    {alpha : Type} (valuation : alpha → Fin 5)
    (letters : List alpha) : Option (Fin 5) :=
  evalFrom none valuation letters

@[simp]
theorem evalFrom_nil
    {alpha : Type} (initial : Option (Fin 5))
    (valuation : alpha → Fin 5) :
    evalFrom initial valuation [] = initial :=
  rfl

@[simp]
theorem evalFrom_cons
    {alpha : Type} (initial : Option (Fin 5))
    (valuation : alpha → Fin 5) (letter : alpha)
    (letters : List alpha) :
    evalFrom initial valuation (letter :: letters) =
      evalFrom (listStep initial (valuation letter)) valuation letters :=
  rfl

theorem evalFrom_some
    {alpha : Type} (initial : Fin 5)
    (valuation : alpha → Fin 5) (letters : List alpha) :
    evalFrom (some initial) valuation letters =
      some
        (letters.foldl
          (fun current letter => table.mul current (valuation letter))
          initial) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter letters induction =>
      simp only [evalFrom_cons, listStep]
      exact induction (table.mul initial (valuation letter))

theorem evalList_toList
    {alpha : Type} (valuation : alpha → Fin 5) (word : Word alpha) :
    evalList valuation word.toList =
      some (table.semigroup.eval valuation word) := by
  cases word with
  | mk head tail =>
      simp only [evalList, evalFrom_cons, listStep, Word.toList,
        Semigroup.eval]
      exact evalFrom_some (valuation head) valuation tail

/-- One-based states 4 and 3 distinguish the tested final variable. -/
def finalLetterValuation
    {alpha : Type} [DecidableEq alpha]
    (tested : alpha) : alpha → Fin 5 :=
  fun letter => if letter = tested then 3 else 2

@[simp]
theorem finalLetterValuation_tested
    {alpha : Type} [DecidableEq alpha] (tested : alpha) :
    finalLetterValuation tested tested = 3 := by
  simp [finalLetterValuation]

theorem finalLetterValuation_other
    {alpha : Type} [DecidableEq alpha]
    {tested letter : alpha} (different : letter ≠ tested) :
    finalLetterValuation tested letter = 2 := by
  simp [finalLetterValuation, different]

private theorem finalLetterValuation_phase
    {alpha : Type} [DecidableEq alpha]
    (tested letter : alpha) :
    finalLetterValuation tested letter = 2 ∨
      finalLetterValuation tested letter = 3 := by
  by_cases equal : letter = tested
  · subst letter
    exact Or.inr (finalLetterValuation_tested tested)
  · exact Or.inl (finalLetterValuation_other equal)

/-- On the two marker states the S5_806 table is the right-zero band, so a
nonempty product records exactly its final input. -/
private theorem mul_final_phase
    (current next : Fin 5)
    (currentPhase : current = 2 ∨ current = 3)
    (nextPhase : next = 2 ∨ next = 3) :
    table.mul current next = next := by
  rcases currentPhase with rfl | rfl <;>
    rcases nextPhase with rfl | rfl <;> decide

private theorem evalFrom_append_final
    {alpha : Type} [DecidableEq alpha]
    (tested : alpha) (current : Fin 5)
    (currentPhase : current = 2 ∨ current = 3) :
    ∀ (body : List alpha) (final : alpha),
      evalFrom (some current) (finalLetterValuation tested)
          (body ++ [final]) =
        some (finalLetterValuation tested final)
  | [], final => by
      rw [List.nil_append, evalFrom_cons, evalFrom_nil]
      simp only [listStep]
      rw [mul_final_phase current
        (finalLetterValuation tested final) currentPhase
        (finalLetterValuation_phase tested final)]
  | letter :: rest, final => by
      rw [List.cons_append, evalFrom_cons]
      simp only [listStep]
      have letterPhase := finalLetterValuation_phase tested letter
      rw [mul_final_phase current
        (finalLetterValuation tested letter) currentPhase letterPhase]
      exact evalFrom_append_final tested
        (finalLetterValuation tested letter) letterPhase rest final

private theorem evalList_append_final
    {alpha : Type} [DecidableEq alpha]
    (tested : alpha) (body : List alpha) (final : alpha) :
    evalList (finalLetterValuation tested) (body ++ [final]) =
      some (finalLetterValuation tested final) := by
  cases body with
  | nil => rfl
  | cons first rest =>
      rw [List.cons_append]
      change
        evalFrom (some (finalLetterValuation tested first))
            (finalLetterValuation tested) (rest ++ [final]) =
          some (finalLetterValuation tested final)
      exact evalFrom_append_final tested
        (finalLetterValuation tested first)
        (finalLetterValuation_phase tested first) rest final

private theorem dropLast_append_componentFinal
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [componentFinal (head :: tail)] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [componentFinal, List.getLastD_cons] using reconstruction

theorem finalLetterEvalList
    (tested head : Nat) (tail : List Nat) :
    evalList (finalLetterValuation tested) (head :: tail) =
      some
        (finalLetterValuation tested
          (componentFinal (head :: tail))) := by
  have evaluated :=
    evalList_append_final tested (head :: tail).dropLast
      (componentFinal (head :: tail))
  rw [dropLast_append_componentFinal head tail] at evaluated
  exact evaluated

theorem finalLetterEvalWord
    (tested : Nat) (word : Word Nat) :
    table.semigroup.eval (finalLetterValuation tested) word =
      finalLetterValuation tested (componentFinal word.toList) := by
  cases word with
  | mk head tail =>
      have listed := finalLetterEvalList tested head tail
      have evaluated :=
        evalList_toList (finalLetterValuation tested) ⟨head, tail⟩
      have evaluated' :
          evalList (finalLetterValuation tested) (head :: tail) =
            some
              (table.semigroup.eval (finalLetterValuation tested)
                ⟨head, tail⟩) := by
        simpa using evaluated
      rw [evaluated'] at listed
      exact Option.some.inj listed

/-- Exact table marker for the only endpoint datum retained by S5_806. -/
theorem valid_sameFinalVariable
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_806.table.semigroup) :
    componentFinal identity.lhs.toList =
      componentFinal identity.rhs.toList := by
  let tested := componentFinal identity.lhs.toList
  let valuation := finalLetterValuation tested
  have evaluations := valid valuation
  have evaluations' :
      table.semigroup.eval (finalLetterValuation tested) identity.lhs =
        table.semigroup.eval (finalLetterValuation tested)
          identity.rhs := by
    simpa [valuation] using evaluations
  have leftDetected := finalLetterEvalWord tested identity.lhs
  have rightDetected := finalLetterEvalWord tested identity.rhs
  have markerEq :
      finalLetterValuation tested
          (componentFinal identity.lhs.toList) =
        finalLetterValuation tested
          (componentFinal identity.rhs.toList) :=
    leftDetected.symm.trans (evaluations'.trans rightDetected)
  by_cases rightEq : componentFinal identity.rhs.toList = tested
  · simpa [tested] using rightEq.symm
  · have impossible := markerEq
    simp [finalLetterValuation, tested, rightEq] at impossible

/-! ## Exact table separation -/

/-- Every identity of the catalogue representative preserves the exact
ordered S5_806 signature. -/
theorem valid_sameConnectedCutSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_806.table.semigroup) :
    SameConnectedCutSignature identity.lhs identity.rhs := by
  have baseEq := valid_sameBaseComponentSignatures identity valid
  have finalEq := valid_sameFinalVariable identity valid
  change
    ConnectedCutSignature.mk
        (connectedComponentSignaturesWord identity.lhs)
        (componentFinal identity.lhs.toList) =
      ConnectedCutSignature.mk
        (connectedComponentSignaturesWord identity.rhs)
        (componentFinal identity.rhs.toList)
  rw [baseEq, finalEq]

/-- Every derivation from the eight laws preserves the exact signature. -/
theorem derives_sameConnectedCutSignature
    {left right : Word Nat} (derivation : Derives basis left right) :
    SameConnectedCutSignature left right := by
  let identity : Identity Nat := ⟨left, right⟩
  exact valid_sameConnectedCutSignature identity <| fun valuation =>
    derivation.sound catalogueModels valuation

end SemigroupBasis.CoRoots.S5_806

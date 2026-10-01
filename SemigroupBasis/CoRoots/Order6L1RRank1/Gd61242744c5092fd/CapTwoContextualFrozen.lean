import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoFrozenCore
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Contextual symmetric RTC of the 198 frozen Gd paths

This off-tree source is the exact closure layer for `FrozenCoreStep`.  It adds
literal two-sided list contexts and either orientation to one step, then takes
only reflexive-transitive closure.  Symmetry, context closure, and substitution
closure are proved operations, not additional generating steps.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis

/-- Substitute nonempty words for every letter of a possibly empty list. -/
def listSubst (substitution : Nat → Word Nat) (letters : List Nat) :
    List Nat :=
  letters.flatMap (fun letter => (substitution letter).toList)

private theorem listSubst_append
    (substitution : Nat → Word Nat) (left right : List Nat) :
    listSubst substitution (left ++ right) =
      listSubst substitution left ++ listSubst substitution right := by
  simp [listSubst]

private theorem listSubst_toList
    (substitution : Nat → Word Nat) (word : Word Nat) :
    listSubst substitution word.toList = (word.bind substitution).toList := by
  simp [listSubst, Word.toList_bind]

inductive FrozenDirection where
  | forward
  | reverse
deriving DecidableEq, Repr

/-- One oriented core path inside a possibly empty literal list context. -/
structure ContextualFrozenWitness where
  forwardSource : Word Nat
  forwardTarget : Word Nat
  core : FrozenCoreAny forwardSource forwardTarget
  direction : FrozenDirection
  front : List Nat
  suffix : List Nat

namespace ContextualFrozenWitness

def coreSource (witness : ContextualFrozenWitness) : Word Nat :=
  match witness.direction with
  | .forward => witness.forwardSource
  | .reverse => witness.forwardTarget

def coreTarget (witness : ContextualFrozenWitness) : Word Nat :=
  match witness.direction with
  | .forward => witness.forwardTarget
  | .reverse => witness.forwardSource

def source (witness : ContextualFrozenWitness) : List Nat :=
  witness.front ++ witness.coreSource.toList ++ witness.suffix

def target (witness : ContextualFrozenWitness) : List Nat :=
  witness.front ++ witness.coreTarget.toList ++ witness.suffix

def flip (witness : ContextualFrozenWitness) : ContextualFrozenWitness :=
  { witness with
      direction :=
        match witness.direction with
        | .forward => .reverse
        | .reverse => .forward }

theorem flip_source (witness : ContextualFrozenWitness) :
    witness.flip.source = witness.target := by
  cases witness with
  | mk forwardSource forwardTarget core direction front suffix =>
      cases direction <;>
        simp [flip, source, target, coreSource, coreTarget]

theorem flip_target (witness : ContextualFrozenWitness) :
    witness.flip.target = witness.source := by
  cases witness with
  | mk forwardSource forwardTarget core direction front suffix =>
      cases direction <;>
        simp [flip, source, target, coreSource, coreTarget]

def subst
    (witness : ContextualFrozenWitness)
    (substitution : Nat → Word Nat) : ContextualFrozenWitness where
  forwardSource := witness.forwardSource.bind substitution
  forwardTarget := witness.forwardTarget.bind substitution
  core := witness.core.subst substitution
  direction := witness.direction
  front := listSubst substitution witness.front
  suffix := listSubst substitution witness.suffix

theorem subst_source
    (witness : ContextualFrozenWitness)
    (substitution : Nat → Word Nat) :
    (witness.subst substitution).source =
      listSubst substitution witness.source := by
  cases witness with
  | mk forwardSource forwardTarget core direction front suffix =>
      cases direction <;>
        simp [subst, source, coreSource, listSubst_append,
          listSubst_toList, List.append_assoc]

theorem subst_target
    (witness : ContextualFrozenWitness)
    (substitution : Nat → Word Nat) :
    (witness.subst substitution).target =
      listSubst substitution witness.target := by
  cases witness with
  | mk forwardSource forwardTarget core direction front suffix =>
      cases direction <;>
        simp [subst, target, coreTarget, listSubst_append,
          listSubst_toList, List.append_assoc]

theorem coreDerives (witness : ContextualFrozenWitness) :
    Derives basis witness.coreSource witness.coreTarget := by
  cases directionEq : witness.direction with
  | forward =>
      simpa [coreSource, coreTarget, directionEq] using witness.core.derives
  | reverse =>
      simpa [coreSource, coreTarget, directionEq] using
        witness.core.derives.symm

theorem listDerives (witness : ContextualFrozenWitness) :
    S5_107.ListDerives basis witness.source witness.target := by
  exact S5_107.ListDerives.context witness.front witness.suffix
    (S5_107.ListDerives.ofWord witness.coreDerives)

end ContextualFrozenWitness

/-- Exactly one oriented contextual instance of one frozen path. -/
def ContextualFrozenStep (left right : List Nat) : Prop :=
  ∃ witness : ContextualFrozenWitness,
    left = witness.source ∧ right = witness.target

theorem contextualFrozenStep_listDerives
    {left right : List Nat}
    (step : ContextualFrozenStep left right) :
    S5_107.ListDerives basis left right := by
  obtain ⟨witness, rfl, rfl⟩ := step
  exact witness.listDerives

theorem contextualFrozenStep_symm
    {left right : List Nat}
    (step : ContextualFrozenStep left right) :
    ContextualFrozenStep right left := by
  obtain ⟨witness, rfl, rfl⟩ := step
  exact ⟨witness.flip, witness.flip_source.symm,
    witness.flip_target.symm⟩

theorem contextualFrozenStep_context
    {left right : List Nat}
    (step : ContextualFrozenStep left right)
    (outerPrefix outerSuffix : List Nat) :
    ContextualFrozenStep
      (outerPrefix ++ left ++ outerSuffix)
      (outerPrefix ++ right ++ outerSuffix) := by
  obtain ⟨witness, rfl, rfl⟩ := step
  let extended : ContextualFrozenWitness :=
    { witness with
        front := outerPrefix ++ witness.front
        suffix := witness.suffix ++ outerSuffix }
  exact ⟨extended,
    by simp [extended, ContextualFrozenWitness.source,
      ContextualFrozenWitness.coreSource, List.append_assoc],
    by simp [extended, ContextualFrozenWitness.target,
      ContextualFrozenWitness.coreTarget, List.append_assoc]⟩

theorem contextualFrozenStep_subst
    {left right : List Nat}
    (step : ContextualFrozenStep left right)
    (substitution : Nat → Word Nat) :
    ContextualFrozenStep
      (listSubst substitution left) (listSubst substitution right) := by
  obtain ⟨witness, rfl, rfl⟩ := step
  exact ⟨witness.subst substitution,
    (witness.subst_source substitution).symm,
    (witness.subst_target substitution).symm⟩

/-- Reflexive-transitive closure of exactly the contextual frozen steps. -/
inductive ContextualFrozenRTC : List Nat → List Nat → Prop where
  | refl (letters : List Nat) : ContextualFrozenRTC letters letters
  | cons {left middle right : List Nat}
      (step : ContextualFrozenStep left middle)
      (rest : ContextualFrozenRTC middle right) :
      ContextualFrozenRTC left right

namespace ContextualFrozenRTC

theorem single
    {left right : List Nat}
    (step : ContextualFrozenStep left right) :
    ContextualFrozenRTC left right :=
  .cons step (.refl right)

theorem trans
    {left middle right : List Nat}
    (first : ContextualFrozenRTC left middle)
    (second : ContextualFrozenRTC middle right) :
    ContextualFrozenRTC left right := by
  induction first generalizing right with
  | refl _ => exact second
  | cons step rest inductionHypothesis =>
      exact .cons step (inductionHypothesis second)

theorem symm
    {left right : List Nat}
    (reachable : ContextualFrozenRTC left right) :
    ContextualFrozenRTC right left := by
  induction reachable with
  | refl letters => exact .refl letters
  | cons step rest inductionHypothesis =>
      exact inductionHypothesis.trans
        (.single (contextualFrozenStep_symm step))

theorem context
    {left right : List Nat}
    (reachable : ContextualFrozenRTC left right)
    (outerPrefix outerSuffix : List Nat) :
    ContextualFrozenRTC
      (outerPrefix ++ left ++ outerSuffix)
      (outerPrefix ++ right ++ outerSuffix) := by
  induction reachable with
  | refl letters => exact .refl _
  | cons step rest inductionHypothesis =>
      exact .cons
        (contextualFrozenStep_context step outerPrefix outerSuffix)
        inductionHypothesis

theorem subst
    {left right : List Nat}
    (reachable : ContextualFrozenRTC left right)
    (substitution : Nat → Word Nat) :
    ContextualFrozenRTC
      (listSubst substitution left) (listSubst substitution right) := by
  induction reachable with
  | refl letters => exact .refl _
  | cons step rest inductionHypothesis =>
      exact .cons
        (contextualFrozenStep_subst step substitution)
        inductionHypothesis

end ContextualFrozenRTC

/-- A forward frozen core instance is one RTC step. -/
theorem contextualFrozenRTC_of_core
    {index : FrozenPathIndex} {left right : Word Nat}
    (core : FrozenCoreStep index left right) :
    ContextualFrozenRTC left.toList right.toList := by
  let witness : ContextualFrozenWitness :=
    { forwardSource := left
      forwardTarget := right
      core := ⟨index, core⟩
      direction := .forward
      front := []
      suffix := [] }
  apply ContextualFrozenRTC.single
  exact ⟨witness,
    by simp [witness, ContextualFrozenWitness.source,
      ContextualFrozenWitness.coreSource],
    by simp [witness, ContextualFrozenWitness.target,
      ContextualFrozenWitness.coreTarget]⟩

theorem contextualFrozenRTC_listDerives
    {left right : List Nat}
    (reachable : ContextualFrozenRTC left right) :
    S5_107.ListDerives basis left right := by
  induction reachable with
  | refl letters => exact S5_107.ListDerives.refl letters
  | cons step rest inductionHypothesis =>
      exact (contextualFrozenStep_listDerives step).trans
        inductionHypothesis

/-- RTC soundness at nonempty word endpoints. -/
theorem contextualFrozenRTC_derives
    {left right : Word Nat}
    (reachable : ContextualFrozenRTC left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [S5_107.listWordOfCons] using
            S5_107.ListDerives.toWord
              (contextualFrozenRTC_listDerives reachable)

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd

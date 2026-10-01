import SemigroupBasis.FiniteVariableRenaming
import SemigroupBasis.Order6.FactorPairJoin

/-!
# Common unrestricted Layer-C machinery for the six heavy rank-two pairs

This file fixes the proof-facing representations shared by the three Layer-C
families.  It contains no bounded oracle premise: every normal-form operation
and every derivability obligation ranges over arbitrary nonempty words.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon

open SemigroupBasis

/-- A semigroup substitution sends every variable to a nonempty word. -/
abbrev Substitution (alpha : Type u) := alpha -> Word alpha

/-- Apply a simultaneous nonempty-word substitution. -/
def applySubstitution (substitution : Substitution alpha)
    (word : Word alpha) : Word alpha :=
  word.bind substitution

/-- Equational derivations are stable under the fixed substitution
representation. -/
theorem Derives.underSubstitution
    {basis : List (Identity alpha)} {left right : Word alpha}
    (derivation : Derives basis left right)
    (substitution : Substitution alpha) :
    Derives basis
      (applySubstitution substitution left)
      (applySubstitution substitution right) := by
  exact Derives.subst derivation substitution

/-- A two-sided semigroup context.  `none` represents an empty side; the core
word is always nonempty. -/
structure Context (alpha : Type u) where
  left : Option (Word alpha)
  right : Option (Word alpha)

namespace Context

/-- Plug a nonempty word into a context.  The two-sided case is deliberately
left associated, matching `Derives.prepend` followed by
`Derives.appendRight`. -/
def plug (context : Context alpha) (word : Word alpha) : Word alpha :=
  match context.left, context.right with
  | none, none => word
  | some pre, none => pre ++ word
  | none, some suffix => word ++ suffix
  | some pre, some suffix => (pre ++ word) ++ suffix

/-- Derivability is stable under arbitrary two-sided contexts. -/
theorem derives_plug
    {basis : List (Identity alpha)} {left right : Word alpha}
    (context : Context alpha) (derivation : Derives basis left right) :
    Derives basis (context.plug left) (context.plug right) := by
  cases context with
  | mk contextLeft contextRight =>
      cases contextLeft with
      | none =>
          cases contextRight with
          | none => simpa only [plug] using derivation
          | some suffix =>
              simpa only [plug] using
                Derives.appendRight derivation suffix
      | some pre =>
          cases contextRight with
          | none =>
              simpa only [plug] using Derives.prepend pre derivation
          | some suffix =>
              simpa only [plug] using
                Derives.appendRight
                  (Derives.prepend pre derivation) suffix

end Context

/-- Binding singleton words is ordinary variable renaming. -/
theorem bind_singleton_eq_map (word : Word alpha) (rename : alpha -> alpha) :
    word.bind (fun letter => Word.singleton (rename letter)) =
      word.map rename := by
  have flatMapSingleton :
      forall letters : List alpha,
        letters.flatMap (fun letter => [rename letter]) =
          letters.map rename := by
    intro letters
    induction letters with
    | nil => rfl
    | cons letter rest induction =>
        simp only [List.flatMap_cons, List.map_cons, induction,
          List.singleton_append]
  apply Word.toList_injective
  rw [Word.toList_bind]
  change
    word.toList.flatMap (fun letter => [rename letter]) =
      (word.map rename).toList
  rw [flatMapSingleton]
  cases word
  rfl

/-- A derivation may be renamed uniformly on both endpoints. -/
theorem Derives.map
    {basis : List (Identity alpha)} {left right : Word alpha}
    (derivation : Derives basis left right) (rename : alpha -> alpha) :
    Derives basis (left.map rename) (right.map rename) := by
  simpa only [bind_singleton_eq_map] using
    Derives.subst derivation (fun letter => Word.singleton (rename letter))

/-- First-occurrence renaming of an arbitrary pair of natural-variable words.
This is only a reconstruction device; it carries no finite-rank completeness
claim. -/
def firstOccurrencePair (left right : Word Nat) :
    FiniteVariableRenaming.Result Nat :=
  FiniteVariableRenaming.normalize left right

theorem firstOccurrencePair_reconstructs (left right : Word Nat) :
    let result := firstOccurrencePair left right
    result.left.map result.inverse = left /\
      result.right.map result.inverse = right := by
  exact FiniteVariableRenaming.normalize_reconstructs left right

/-- Any derivation between the first-occurrence-renamed endpoints reconstructs
to a derivation between the original arbitrary words. -/
theorem derives_of_firstOccurrencePair
    {basis : List (Identity Nat)} (left right : Word Nat)
    (derivation :
      let result := firstOccurrencePair left right
      Derives basis result.left result.right) :
    Derives basis left right := by
  let result := firstOccurrencePair left right
  have renamed :
      Derives basis
        (result.left.map result.inverse)
        (result.right.map result.inverse) :=
    Derives.map derivation result.inverse
  have reconstructs := firstOccurrencePair_reconstructs left right
  rw [reconstructs.1, reconstructs.2] at renamed
  exact renamed

/-- The reachable part of a deterministic normal-form construction. -/
structure ReachableNormalForm (basis : List (Identity alpha)) where
  normal : Word alpha -> Word alpha
  derives_normal : forall word : Word alpha, Derives basis word (normal word)

/-- The unrestricted equality obligation imposed by the two factor theories. -/
def FactorSeparates
    {B : Type v} {C : Type w} {alpha : Type z}
    (H : Semigroup B) (K : Semigroup C)
    (normal : Word alpha -> Word alpha) : Prop :=
  forall identity : Identity alpha,
    identity.SatisfiedBy H ->
      identity.SatisfiedBy K ->
        normal identity.lhs = normal identity.rhs

namespace ReachableNormalForm

/-- Add the pair-specific unrestricted factor-equality proof to obtain the
reviewed public `IntersectionNormalizer` API. -/
def toIntersectionNormalizer
    {B : Type v} {C : Type w} {alpha : Type z}
    {H : Semigroup B} {K : Semigroup C}
    {basis : List (Identity alpha)}
    (reachable : ReachableNormalForm basis)
    (separates : FactorSeparates H K reachable.normal) :
    IntersectionNormalizer H K basis where
  normal := reachable.normal
  derives_normal := reachable.derives_normal
  normal_eq_of_factor_valid := separates

end ReachableNormalForm

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon

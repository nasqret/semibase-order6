import Lean.Data.Json
import SemigroupBasis.Equational

namespace SemigroupBasis
namespace ChainReplay

/-- The orientation in which a basis identity is used. -/
inductive Direction where
  | forward
  | backward
deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

/--
A serialized equational rewrite over an alphabet `α`.

`substitution[denseIndex x]` is the nonempty word substituted for `x`.
Variables beyond the end of the list are left unchanged. Generated finite
certificates provide one image for every dense index; the fallback preserves
the finite-support convention used by the existing `Nat` certificates.
-/
structure Step (α : Type u) where
  lawIndex : Nat
  direction : Direction
  leftContext : List α
  rightContext : List α
  substitution : List (List α)
deriving Repr, DecidableEq, Lean.ToJson, Lean.FromJson

/-- A derivation certificate is a serial list of checked rewrites. -/
abbrev Chain (α : Type u) := List (Step α)

/-- The canonical dense index for the existing `Nat` certificate API. -/
def natDenseIndex : Nat → Nat := id

/-- The canonical dense index for a finite alphabet. -/
def finDenseIndex {n : Nat} : Fin n → Nat := fun x => x.val

/-- Decode the list representation of a nonempty semigroup word. -/
def wordOfList? {α : Type u} : List α → Option (Word α)
  | [] => none
  | head :: tail => some ⟨head, tail⟩

/-- Reject a substitution as soon as one of its displayed images is empty. -/
def decodeSubstitution {α : Type u} :
    List (List α) → Option (List (Word α))
  | [] => some []
  | image :: rest => do
      let word ← wordOfList? image
      let words ← decodeSubstitution rest
      pure (word :: words)

/--
Interpret a dense finite substitution table. Omitted indices map to singleton
words so that `Nat` certificates can retain finite-support substitutions.
-/
def substitutionAt {α : Type u} (denseIndex : α → Nat)
    (images : List (Word α)) (letter : α) : Word α :=
  (images[denseIndex letter]?).getD (Word.singleton letter)

namespace Context

private def appendList {α : Type u} (word : Word α) : List α → Word α
  | [] => word
  | head :: tail => word ++ ⟨head, tail⟩

/-- Put a nonempty word inside possibly empty list contexts. -/
def wrap {α : Type u} (leftContext : List α) (middle : Word α)
    (rightContext : List α) : Word α :=
  match leftContext with
  | [] => appendList middle rightContext
  | head :: tail =>
      appendList (⟨head, tail⟩ ++ middle) rightContext

@[simp]
theorem wrap_toList {α : Type u} (leftContext : List α) (middle : Word α)
    (rightContext : List α) :
    (wrap leftContext middle rightContext).toList =
      leftContext ++ middle.toList ++ rightContext := by
  cases leftContext <;> cases rightContext <;>
    simp [wrap, appendList, Word.toList, List.append_assoc]

/-- Existing `Derives` context constructors implement `wrap`. -/
theorem derives_wrap {α : Type u} {basis : List (Identity α)}
    {left right : Word α}
    (derivation : Derives basis left right)
    (leftContext rightContext : List α) :
    Derives basis
      (wrap leftContext left rightContext)
      (wrap leftContext right rightContext) := by
  cases leftContext with
  | nil =>
      cases rightContext with
      | nil =>
          simpa [wrap, appendList] using derivation
      | cons head tail =>
          simpa [wrap, appendList] using
            (Derives.appendRight derivation (Word.mk head tail))
  | cons leftHead leftTail =>
      cases rightContext with
      | nil =>
          simpa [wrap, appendList] using
            (Derives.prepend (Word.mk leftHead leftTail) derivation)
      | cons rightHead rightTail =>
          simpa [wrap, appendList] using
            (Derives.appendRight
              (Derives.prepend
                (Word.mk leftHead leftTail) derivation)
              (Word.mk rightHead rightTail))

end Context

def Direction.source {α : Type u} (direction : Direction)
    (law : Identity α) (denseIndex : α → Nat)
    (images : List (Word α)) : Word α :=
  match direction with
  | .forward => law.lhs.bind (substitutionAt denseIndex images)
  | .backward => law.rhs.bind (substitutionAt denseIndex images)

def Direction.target {α : Type u} (direction : Direction)
    (law : Identity α) (denseIndex : α → Nat)
    (images : List (Word α)) : Word α :=
  match direction with
  | .forward => law.rhs.bind (substitutionAt denseIndex images)
  | .backward => law.lhs.bind (substitutionAt denseIndex images)

theorem Direction.derives {α : Type u} {basis : List (Identity α)}
    (direction : Direction) {law : Identity α}
    (member : law ∈ basis) (denseIndex : α → Nat)
    (images : List (Word α)) :
    Derives basis
      (direction.source law denseIndex images)
      (direction.target law denseIndex images) := by
  have instantiated :=
    Derives.subst
      (Derives.fromBasis (e := law) member)
      (substitutionAt denseIndex images)
  cases direction with
  | forward =>
      exact instantiated
  | backward =>
      exact Derives.symm instantiated

private theorem law_mem_of_getElem?_eq_some
    {α : Type u} {basis : List (Identity α)} {law : Identity α} {index : Nat}
    (selected : basis[index]? = some law) :
    law ∈ basis := by
  rcases List.getElem?_eq_some_iff.mp selected with
    ⟨inBounds, atIndex⟩
  rw [← atIndex]
  exact List.getElem_mem inBounds

/--
Execute one checked rewrite. Failure means the law index is invalid, a
displayed substitution image is empty, or the current word is not exactly the
recorded contextual instance.
-/
def Step.replay {α : Type u} [DecidableEq α] (step : Step α)
    (denseIndex : α → Nat) (basis : List (Identity α))
    (current : Word α) : Option (Word α) :=
  match basis[step.lawIndex]? with
  | none => none
  | some law =>
      match decodeSubstitution step.substitution with
      | none => none
      | some images =>
          let expected :=
            Context.wrap step.leftContext
              (step.direction.source law denseIndex images) step.rightContext
          if current = expected then
            some <|
              Context.wrap step.leftContext
                (step.direction.target law denseIndex images) step.rightContext
          else
            none

/-- A successful executable step is an ordinary equational derivation. -/
theorem Step.replay_sound {α : Type u} [DecidableEq α]
    {denseIndex : α → Nat} {basis : List (Identity α)} {step : Step α}
    {current next : Word α}
    (success : step.replay denseIndex basis current = some next) :
    Derives basis current next := by
  unfold Step.replay at success
  cases selected : basis[step.lawIndex]? with
  | none =>
      simp [selected] at success
  | some law =>
      cases decoded : decodeSubstitution step.substitution with
      | none =>
          simp [selected, decoded] at success
      | some images =>
          simp only [selected, decoded] at success
          by_cases input :
              current =
                Context.wrap step.leftContext
                  (step.direction.source law denseIndex images)
                  step.rightContext
          · simp only [if_pos input, Option.some.injEq] at success
            rw [input, ← success]
            exact Context.derives_wrap
              (step.direction.derives
                (law_mem_of_getElem?_eq_some selected) denseIndex images)
              step.leftContext step.rightContext
          · simp [input] at success

/-- Replay every step from left to right, returning the final word on success. -/
def replay {α : Type u} [DecidableEq α] (denseIndex : α → Nat)
    (basis : List (Identity α)) :
    Word α → Chain α → Option (Word α)
  | current, [] => some current
  | current, step :: rest =>
      match step.replay denseIndex basis current with
      | none => none
      | some next => replay denseIndex basis next rest

/-- Boolean endpoint checker for serialized chains. -/
def check {α : Type u} [DecidableEq α] (denseIndex : α → Nat)
    (basis : List (Identity α)) (start target : Word α)
    (chain : Chain α) : Bool :=
  decide (replay denseIndex basis start chain = some target)

/-- Encode an existing `Nat` chain using the derived JSON representation. -/
def encode (chain : Chain Nat) : Lean.Json :=
  Lean.toJson chain

/-- Decode an existing `Nat` JSON chain, reporting malformed fields. -/
def decode (json : Lean.Json) : Except String (Chain Nat) :=
  Lean.fromJson? json

/-- Successful chain replay yields the repository's existing `Derives`. -/
theorem replay_sound {α : Type u} [DecidableEq α]
    {denseIndex : α → Nat} {basis : List (Identity α)}
    {start target : Word α} {chain : Chain α}
    (success : replay denseIndex basis start chain = some target) :
    Derives basis start target := by
  induction chain generalizing start with
  | nil =>
      have equality : start = target := by
        simpa [replay] using success
      rw [equality]
      exact Derives.refl target
  | cons step rest ih =>
      cases stepResult : step.replay denseIndex basis start with
      | none =>
          simp [replay, stepResult] at success
      | some middle =>
          have restSuccess :
              replay denseIndex basis middle rest = some target := by
            simpa [replay, stepResult] using success
          exact Derives.trans
            (Step.replay_sound stepResult)
            (ih restSuccess)

/-- The Boolean checker has the same proof-producing soundness boundary. -/
theorem check_sound {α : Type u} [DecidableEq α]
    {denseIndex : α → Nat} {basis : List (Identity α)}
    {start target : Word α} {chain : Chain α}
    (success : check denseIndex basis start target chain = true) :
    Derives basis start target := by
  unfold check at success
  exact replay_sound (of_decide_eq_true success)

end ChainReplay
end SemigroupBasis

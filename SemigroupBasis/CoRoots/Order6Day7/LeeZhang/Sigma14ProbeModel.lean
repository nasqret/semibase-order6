import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14WordStages
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12Semantics

/-! Shared finite probe interface for the six exact Sigma14 targets approved in
msg-0424. Its fields are only a concrete embedding and finite multiplication
equations; unrestricted separation is proved below and in the next modules.
The original fable screen2 replay at MAX7 and MAX8 preceded this proof module.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

open SemigroupBasis
open S6_2708.Sigma12
open S4_71Suffix (put)

structure ProbeModel (G : Semigroup (Fin 6)) (swapping : Bool) where
  capEmbedding : Embedding Examples.commutativeExponentThree.semigroup G
  simpleMarker : Fin 6
  driftMarker : Fin 6
  pairLast : Fin 6
  pairMark : Fin 6
  pairMiddle : Fin 6
  mul_zero : ∀ value, G.mul value 0 = 0
  neutral_one : G.mul 5 1 = 1
  mark_one : G.mul 4 1 = 0
  neutral_simple : G.mul 5 simpleMarker = simpleMarker
  mark_simple : G.mul 4 simpleMarker = if swapping then 1 else 0
  neutral_drift : G.mul 5 driftMarker = driftMarker
  mark_drift : G.mul 4 driftMarker = 0
  neutral_neutral : G.mul 5 5 = 5
  mark_neutral : G.mul 4 5 = driftMarker
  neutral_mark : G.mul 5 4 = simpleMarker
  mark_mark : G.mul 4 4 = 1
  simple_ne_zero : simpleMarker ≠ 0
  simple_ne_one : simpleMarker ≠ 1
  simple_ne_neutral : simpleMarker ≠ 5
  drift_ne_simple : driftMarker ≠ simpleMarker
  drift_ne_one : driftMarker ≠ 1
  pair_neutral_last : G.mul 5 pairLast = pairMiddle
  pair_mark_last : G.mul pairMark pairLast = 1
  pair_neutral_middle : G.mul 5 pairMiddle = pairMiddle
  pair_mark_middle : G.mul pairMark pairMiddle = 0
  pair_mark_one : G.mul pairMark 1 = 0

def Equivalent (G : Semigroup (Fin 6)) (left right : Word Nat) : Prop :=
  ∀ valuation, G.eval valuation left = G.eval valuation right

theorem Equivalent.symm {G : Semigroup (Fin 6)} {left right : Word Nat}
    (same : Equivalent G left right) : Equivalent G right left :=
  fun valuation => (same valuation).symm

variable {G : Semigroup (Fin 6)} {swapping : Bool}

theorem caps_of_equivalent (model : ProbeModel G swapping) (left right : Word Nat)
    (same : Equivalent G left right) : SameCaps left.toList right.toList :=
  Examples.exponentValid_capped_count_eq ⟨left, right⟩
    (model.capEmbedding.pullback_identity ⟨left, right⟩ same)

def prefixEval (G : Semigroup (Fin 6)) (valuation : Nat → Fin 6) : List Nat → Fin 6 → Fin 6
  | [], value => value
  | letter :: rest, value => G.mul (valuation letter) (prefixEval G valuation rest value)

theorem eval_put (valuation : Nat → Fin 6) (front : List Nat) (suffix : Word Nat) :
    G.eval valuation (put front suffix) = prefixEval G valuation front (G.eval valuation suffix) := by
  induction front with
  | nil => rfl
  | cons letter rest ih =>
      simp only [put, Semigroup.eval_append, Semigroup.eval_singleton, prefixEval, ih]

theorem eval_framed (valuation : Nat → Fin 6) (front : List Nat) (penultimate last : Nat) :
    G.eval valuation (framed front penultimate last) =
      prefixEval G valuation front (G.mul (valuation penultimate) (valuation last)) := by
  rw [framed, eval_put]
  rfl

theorem prefixEval_zero (model : ProbeModel G swapping) (valuation : Nat → Fin 6) (front : List Nat) :
    prefixEval G valuation front 0 = 0 := by
  induction front with
  | nil => rfl
  | cons letter rest ih => rw [prefixEval, ih, model.mul_zero]

def oneFall (count : Nat) : Fin 6 := if count = 0 then 1 else 0
def simpleFall (model : ProbeModel G swapping) (count : Nat) : Fin 6 :=
  if count = 0 then model.simpleMarker else if count = 1 then (if swapping then 1 else 0) else 0
def drift (model : ProbeModel G swapping) (count : Nat) : Fin 6 :=
  if count = 0 then 5 else if count = 1 then model.driftMarker else 0

theorem mark_oneFall (model : ProbeModel G swapping) (count : Nat) :
    G.mul 4 (oneFall count) = oneFall (count + 1) := by
  cases count <;> simp [oneFall, model.mark_one, model.mul_zero]

theorem neutral_oneFall (model : ProbeModel G swapping) (count : Nat) :
    G.mul 5 (oneFall count) = oneFall count := by
  cases count <;> simp [oneFall, model.neutral_one, model.mul_zero]

theorem mark_simpleFall (model : ProbeModel G swapping) (count : Nat) :
    G.mul 4 (simpleFall model count) = simpleFall model (count + 1) := by
  cases count with
  | zero => simp [simpleFall, model.mark_simple]
  | succ rest =>
      cases rest <;> cases swapping <;>
        simp [simpleFall, model.mark_one, model.mul_zero]

theorem neutral_simpleFall (model : ProbeModel G swapping) (count : Nat) :
    G.mul 5 (simpleFall model count) = simpleFall model count := by
  cases count with
  | zero => simp [simpleFall, model.neutral_simple]
  | succ rest =>
      cases rest <;> cases swapping <;>
        simp [simpleFall, model.neutral_one, model.mul_zero]

theorem mark_drift (model : ProbeModel G swapping) (count : Nat) :
    G.mul 4 (drift model count) = drift model (count + 1) := by
  cases count with
  | zero => simp [drift, model.mark_neutral]
  | succ rest => cases rest <;> simp [drift, model.mark_drift, model.mul_zero]

theorem neutral_drift (model : ProbeModel G swapping) (count : Nat) :
    G.mul 5 (drift model count) = drift model count := by
  cases count with
  | zero => simp [drift, model.neutral_neutral]
  | succ rest => cases rest <;> simp [drift, model.neutral_drift, model.mul_zero]

theorem oneFall_eq_one_iff (count : Nat) : oneFall count = 1 ↔ count = 0 := by
  cases count <;> simp [oneFall]

theorem oneFall_ne_simple (model : ProbeModel G swapping) (count : Nat) :
    oneFall count ≠ model.simpleMarker := by
  cases count <;> simp [oneFall, Ne.symm model.simple_ne_zero, Ne.symm model.simple_ne_one]

theorem simpleFall_eq_simple_iff (model : ProbeModel G swapping) (count : Nat) :
    simpleFall model count = model.simpleMarker ↔ count = 0 := by
  cases count with
  | zero => simp [simpleFall]
  | succ rest =>
      cases rest <;> cases swapping <;>
        simp [simpleFall, Ne.symm model.simple_ne_zero, Ne.symm model.simple_ne_one]

theorem simpleFall_eq_one_iff (model : ProbeModel G swapping) (count : Nat) :
    simpleFall model count = 1 ↔ count = 1 ∧ swapping = true := by
  cases count with
  | zero => simp [simpleFall, model.simple_ne_one]
  | succ rest => cases rest <;> cases swapping <;> simp [simpleFall]

theorem drift_ne_simple (model : ProbeModel G swapping) (count : Nat) :
    drift model count ≠ model.simpleMarker := by
  cases count with
  | zero => simpa [drift] using Ne.symm model.simple_ne_neutral
  | succ rest =>
      cases rest <;> simp [drift, model.drift_ne_simple, Ne.symm model.simple_ne_zero]

theorem drift_ne_one (model : ProbeModel G swapping) (count : Nat) :
    drift model count ≠ 1 := by
  cases count with
  | zero => change (5 : Fin 6) ≠ 1; decide
  | succ rest => cases rest <;> simp [drift, model.drift_ne_one]

def marker (selected letter : Nat) : Fin 6 := if letter = selected then 4 else 5

theorem marker_prefix (fall : Nat → Fin 6)
    (markStep : ∀ count, G.mul 4 (fall count) = fall (count + 1))
    (neutralStep : ∀ count, G.mul 5 (fall count) = fall count)
    (selected : Nat) (front : List Nat) :
    prefixEval G (marker selected) front (fall 0) = fall (front.count selected) := by
  induction front with
  | nil => rfl
  | cons letter rest ih =>
      by_cases equal : letter = selected
      · subst letter
        simp only [prefixEval, marker, List.count_cons_self, ih]
        exact markStep _
      · simp only [prefixEval, marker, if_neg equal, List.count_cons_of_ne equal, ih]
        exact neutralStep _

theorem marker_prefix_one (model : ProbeModel G swapping) (selected : Nat) (front : List Nat) :
    prefixEval G (marker selected) front 1 = oneFall (front.count selected) :=
  marker_prefix oneFall (mark_oneFall model) (neutral_oneFall model) selected front

theorem marker_prefix_simple (model : ProbeModel G swapping) (selected : Nat) (front : List Nat) :
    prefixEval G (marker selected) front model.simpleMarker = simpleFall model (front.count selected) :=
  marker_prefix (simpleFall model) (mark_simpleFall model) (neutral_simpleFall model) selected front

theorem marker_prefix_neutral (model : ProbeModel G swapping) (selected : Nat) (front : List Nat) :
    prefixEval G (marker selected) front 5 = drift model (front.count selected) :=
  marker_prefix (drift model) (mark_drift model) (neutral_drift model) selected front

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

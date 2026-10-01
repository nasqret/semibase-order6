import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441Derivations

/-!
# Unrestricted prefix and endpoint separators for the literal S6_5441

Two unary probes recover exactly the content before the last two letters.
Their nonzero states recover free penultimate/final letters. A binary probe
recovers the last letter even when it is bound and the penultimate is free.
All formulas are proved by arbitrary-list induction, not by bounded words.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441

open SemigroupBasis

def probeValuation (chosen other : Fin 6) (selected letter : Nat) : Fin 6 :=
  if letter = selected then chosen else other

def lowEval (word : Word Nat) (selected : Nat) : Fin 6 :=
  table.semigroup.eval (probeValuation 2 5 selected) word

def highEval (word : Word Nat) (selected : Nat) : Fin 6 :=
  table.semigroup.eval (probeValuation 3 4 selected) word

def crossValuation (marker selected letter : Nat) : Fin 6 :=
  if letter = marker then 2 else if letter = selected then 5 else 4

def crossEval (word : Word Nat) (marker selected : Nat) : Fin 6 :=
  table.semigroup.eval (crossValuation marker selected) word

structure ProbeEquivalent (left right : Word Nat) : Prop where
  low : ∀ selected, lowEval left selected = lowEval right selected
  high : ∀ selected, highEval left selected = highEval right selected
  cross : ∀ marker selected, crossEval left marker selected = crossEval right marker selected

theorem ProbeEquivalent.symm {left right : Word Nat} (same : ProbeEquivalent left right) :
    ProbeEquivalent right left :=
  ⟨fun selected => (same.low selected).symm, fun selected => (same.high selected).symm,
    fun marker selected => (same.cross marker selected).symm⟩

theorem valid_probeEquivalent {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) : ProbeEquivalent left right :=
  ⟨fun selected => valid (probeValuation 2 5 selected),
    fun selected => valid (probeValuation 3 4 selected),
    fun marker selected => valid (crossValuation marker selected)⟩

private theorem frame_cons (head : Nat) (front : List Nat) (penultimate last : Nat) :
    framedWord (head :: front) penultimate last =
      Word.singleton head ++ framedWord front penultimate last := by
  apply Word.toList_injective
  simp only [framedWord, PrefixTwoEndpoint.framedWord_toList, Word.toList_append,
    Word.toList_singleton] <;> rfl

private theorem eval_frame_cons (valuation : Nat → Fin 6)
    (head : Nat) (front : List Nat) (penultimate last : Nat) :
    table.semigroup.eval valuation (framedWord (head :: front) penultimate last) =
      mul (valuation head) (table.semigroup.eval valuation (framedWord front penultimate last)) := by
  simpa only [Semigroup.eval_append, Semigroup.eval_singleton] using
    congrArg (table.semigroup.eval valuation) (frame_cons head front penultimate last)

private theorem zero_right (value : Fin 6) : mul value 0 = 0 := by decide +revert

private theorem two_kills_product (left right : Fin 6) : mul 2 (mul left right) = 0 := by decide +revert
private theorem three_kills_product (left right : Fin 6) : mul 3 (mul left right) = 0 := by decide +revert
private theorem four_passes_product (left right : Fin 6) : mul 4 (mul left right) = mul left right := by decide +revert
private theorem five_passes_product (left right : Fin 6) : mul 5 (mul left right) = mul left right := by decide +revert

private theorem probe_frame_formula (chosen other : Fin 6) (selected : Nat)
    (front : List Nat) (penultimate last : Nat)
    (kill : ∀ left right, mul chosen (mul left right) = 0)
    (pass : ∀ left right, mul other (mul left right) = mul left right) :
    table.semigroup.eval (probeValuation chosen other selected) (framedWord front penultimate last) =
      if selected ∈ front then 0 else
        mul (probeValuation chosen other selected penultimate) (probeValuation chosen other selected last) := by
  induction front with
  | nil => rfl
  | cons head tail ih =>
      rw [eval_frame_cons, ih]
      by_cases present : selected ∈ tail
      · simp [present, zero_right]
      · rw [if_neg present]
        by_cases chosenHead : head = selected
        · subst head
          have value : probeValuation chosen other selected selected = chosen := by simp [probeValuation]
          rw [value, kill]
          simp
        · have value : probeValuation chosen other selected head = other := by
            simp [probeValuation, chosenHead]
          rw [value, pass]
          simp [present, Ne.symm chosenHead]

def lowBoundary (penultimate last selected : Nat) : Fin 6 :=
  if penultimate = selected then (if last = selected then 0 else 1)
  else if last = selected then 2 else 4

def highBoundary (penultimate last selected : Nat) : Fin 6 :=
  if penultimate = selected then (if last = selected then 1 else 0)
  else if last = selected then 2 else 4

private theorem low_boundary (penultimate last selected : Nat) :
    mul (probeValuation 2 5 selected penultimate) (probeValuation 2 5 selected last) =
      lowBoundary penultimate last selected := by
  by_cases penultimateChosen : penultimate = selected <;> by_cases lastChosen : last = selected <;>
    simp [probeValuation, lowBoundary, penultimateChosen, lastChosen, mul]

private theorem high_boundary (penultimate last selected : Nat) :
    mul (probeValuation 3 4 selected penultimate) (probeValuation 3 4 selected last) =
      highBoundary penultimate last selected := by
  by_cases penultimateChosen : penultimate = selected <;> by_cases lastChosen : last = selected <;>
    simp [probeValuation, highBoundary, penultimateChosen, lastChosen, mul]

theorem low_frame (front : List Nat) (penultimate last selected : Nat) :
    lowEval (framedWord front penultimate last) selected =
      if selected ∈ front then 0 else lowBoundary penultimate last selected := by
  unfold lowEval
  rw [probe_frame_formula 2 5 selected front penultimate last two_kills_product five_passes_product,
    low_boundary]

theorem high_frame (front : List Nat) (penultimate last selected : Nat) :
    highEval (framedWord front penultimate last) selected =
      if selected ∈ front then 0 else highBoundary penultimate last selected := by
  unfold highEval
  rw [probe_frame_formula 3 4 selected front penultimate last three_kills_product four_passes_product,
    high_boundary]

theorem probe_prefix_iff (front : List Nat) (penultimate last selected : Nat) :
    (lowEval (framedWord front penultimate last) selected = 0 ∧
      highEval (framedWord front penultimate last) selected = 0) ↔ selected ∈ front := by
  rw [low_frame, high_frame]
  by_cases present : selected ∈ front <;>
    by_cases penultimateChosen : penultimate = selected <;> by_cases lastChosen : last = selected <;>
    simp [present, lowBoundary, highBoundary, penultimateChosen, lastChosen]

theorem probe_penultimate_free_iff (front : List Nat) (penultimate last selected : Nat) :
    (lowEval (framedWord front penultimate last) selected = 1 ∨
      highEval (framedWord front penultimate last) selected = 1) ↔
        penultimate = selected ∧ selected ∉ front := by
  rw [low_frame, high_frame]
  by_cases present : selected ∈ front <;>
    by_cases penultimateChosen : penultimate = selected <;> by_cases lastChosen : last = selected <;>
    simp [present, lowBoundary, highBoundary, penultimateChosen, lastChosen]

theorem probe_last_free_iff (front : List Nat) (penultimate last selected : Nat) :
    (lowEval (framedWord front penultimate last) selected = 2 ∨
      highEval (framedWord front penultimate last) selected = 1) ↔
        last = selected ∧ selected ∉ front := by
  rw [low_frame, high_frame]
  by_cases present : selected ∈ front <;>
    by_cases penultimateChosen : penultimate = selected <;> by_cases lastChosen : last = selected <;>
    simp [present, lowBoundary, highBoundary, penultimateChosen, lastChosen]

theorem high_frame_ne_three (front : List Nat) (penultimate last selected : Nat) :
    highEval (framedWord front penultimate last) selected ≠ 3 := by
  rw [high_frame]
  by_cases present : selected ∈ front <;>
    by_cases penultimateChosen : penultimate = selected <;> by_cases lastChosen : last = selected <;>
    simp [present, highBoundary, penultimateChosen, lastChosen]

private theorem cross_frame_formula (front : List Nat) (penultimate last marker selected : Nat)
    (absent : marker ∉ front) :
    crossEval (framedWord front penultimate last) marker selected =
      mul (crossValuation marker selected penultimate) (crossValuation marker selected last) := by
  induction front with
  | nil => rfl
  | cons head tail ih =>
      have headDifferent : head ≠ marker := by
        intro equal
        exact absent (List.mem_cons.mpr (Or.inl equal.symm))
      have tailAbsent : marker ∉ tail := fun member => absent (List.Mem.tail head member)
      unfold crossEval at ih ⊢
      rw [eval_frame_cons, ih tailAbsent]
      by_cases chosenHead : head = selected
      · have value : crossValuation marker selected head = 5 := by
          simp only [crossValuation, if_neg headDifferent, if_pos chosenHead]
        rw [value, five_passes_product]
      · have value : crossValuation marker selected head = 4 := by
          simp only [crossValuation, if_neg headDifferent, if_neg chosenHead]
        rw [value, four_passes_product]

theorem cross_free_penultimate (front : List Nat) (penultimate last selected : Nat)
    (absent : penultimate ∉ front) (different : last ≠ penultimate) :
    crossEval (framedWord front penultimate last) penultimate selected =
      if last = selected then 1 else 0 := by
  rw [cross_frame_formula front penultimate last penultimate selected absent]
  have penultimateValue : crossValuation penultimate selected penultimate = 2 := by
    simp [crossValuation]
  have lastValue : crossValuation penultimate selected last = (if last = selected then 5 else 4) := by
    simp only [crossValuation, if_neg different]
  rw [penultimateValue, lastValue]
  by_cases chosenLast : last = selected <;>
    simp [chosenLast, mul]

theorem singleton_not_probeEquivalent_frame (letter penultimate last : Nat) (front : List Nat) :
    ¬ ProbeEquivalent (Word.singleton letter) (framedWord front penultimate last) := by
  intro same
  have equal := same.high letter
  have value : highEval (Word.singleton letter) letter = 3 := by
    simp [highEval, probeValuation]
  exact high_frame_ne_three front penultimate last letter (equal.symm.trans value)

theorem singleton_eq_of_probeEquivalent (left right : Nat)
    (same : ProbeEquivalent (Word.singleton left) (Word.singleton right)) : left = right := by
  apply Decidable.byContradiction
  intro different
  have equal := same.high left
  simp [highEval, probeValuation, Ne.symm different] at equal

/-- Every premise of the shared derivation theorem is recovered from actual
table evaluations. The binary probe prevents losing a bound final letter
when the penultimate letter is free. -/
theorem derivesFramesOfProbeEquivalentWith (derivationBasis : List (Identity Nat))
    (rules : PrefixTwoEndpoint.Rules derivationBasis)
    (front otherFront : List Nat) (penultimate last otherPenultimate otherLast : Nat)
    (same : ProbeEquivalent (framedWord front penultimate last)
      (framedWord otherFront otherPenultimate otherLast)) :
    Derives derivationBasis (framedWord front penultimate last)
      (framedWord otherFront otherPenultimate otherLast) := by
  have content : ∀ letter, letter ∈ front ↔ letter ∈ otherFront := by
    intro letter
    rw [← probe_prefix_iff front penultimate last letter,
      ← probe_prefix_iff otherFront otherPenultimate otherLast letter,
      same.low letter, same.high letter]
  have penultimateKey : penultimate = otherPenultimate ∨
      (penultimate ∈ front ∧ otherPenultimate ∈ otherFront) := by
    by_cases equal : penultimate = otherPenultimate
    · exact Or.inl equal
    · apply Or.inr
      constructor
      · apply Decidable.byContradiction
        intro free
        have marked := (probe_penultimate_free_iff front penultimate last penultimate).2 ⟨rfl, free⟩
        rw [same.low penultimate, same.high penultimate] at marked
        exact equal ((probe_penultimate_free_iff otherFront otherPenultimate otherLast penultimate).1 marked).1.symm
      · apply Decidable.byContradiction
        intro free
        have marked := (probe_penultimate_free_iff otherFront otherPenultimate otherLast otherPenultimate).2 ⟨rfl, free⟩
        rw [← same.low otherPenultimate, ← same.high otherPenultimate] at marked
        exact equal ((probe_penultimate_free_iff front penultimate last otherPenultimate).1 marked).1
  have lastKey : last = otherLast ∨ (penultimate ∈ front ∧ otherPenultimate ∈ otherFront ∧
      last ∈ front ∧ otherLast ∈ otherFront) := by
    by_cases equal : last = otherLast
    · exact Or.inl equal
    · have lastInside : last ∈ front := by
        apply Decidable.byContradiction
        intro free
        have marked := (probe_last_free_iff front penultimate last last).2 ⟨rfl, free⟩
        rw [same.low last, same.high last] at marked
        exact equal ((probe_last_free_iff otherFront otherPenultimate otherLast last).1 marked).1.symm
      have otherLastInside : otherLast ∈ otherFront := by
        apply Decidable.byContradiction
        intro free
        have marked := (probe_last_free_iff otherFront otherPenultimate otherLast otherLast).2 ⟨rfl, free⟩
        rw [← same.low otherLast, ← same.high otherLast] at marked
        exact equal ((probe_last_free_iff front penultimate last otherLast).1 marked).1
      have penultimateInside : penultimate ∈ front := by
        apply Decidable.byContradiction
        intro free
        have marked := (probe_penultimate_free_iff front penultimate last penultimate).2 ⟨rfl, free⟩
        rw [same.low penultimate, same.high penultimate] at marked
        obtain ⟨otherEqual, otherFree⟩ :=
          (probe_penultimate_free_iff otherFront otherPenultimate otherLast penultimate).1 marked
        have lastDifferent : last ≠ penultimate := by
          intro lastEqual
          exact free (lastEqual ▸ lastInside)
        have otherLastDifferent : otherLast ≠ penultimate := by
          intro lastEqual
          exact otherFree (lastEqual ▸ otherLastInside)
        have crossEqual := same.cross penultimate last
        rw [otherEqual] at crossEqual
        rw [cross_free_penultimate front penultimate last last free lastDifferent,
          cross_free_penultimate otherFront penultimate otherLast last otherFree otherLastDifferent] at crossEqual
        simp [Ne.symm equal] at crossEqual
      have otherPenultimateInside : otherPenultimate ∈ otherFront := by
        rcases penultimateKey with penultimateEqual | ⟨_, present⟩
        · have present := (content penultimate).1 penultimateInside
          simpa only [penultimateEqual] using present
        · exact present
      exact Or.inr ⟨penultimateInside, otherPenultimateInside, lastInside, otherLastInside⟩
  exact rules.derivesFramesOfPrefixEndpoint front otherFront penultimate last otherPenultimate otherLast
    content penultimateKey lastKey

theorem derivesFramesOfProbeEquivalent
    (front otherFront : List Nat) (penultimate last otherPenultimate otherLast : Nat)
    (same : ProbeEquivalent (framedWord front penultimate last)
      (framedWord otherFront otherPenultimate otherLast)) :
    Derives basis (framedWord front penultimate last)
      (framedWord otherFront otherPenultimate otherLast) :=
  derivesFramesOfProbeEquivalentWith basis calculus front otherFront
    penultimate last otherPenultimate otherLast same

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_5441

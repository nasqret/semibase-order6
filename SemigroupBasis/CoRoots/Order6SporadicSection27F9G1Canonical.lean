import SemigroupBasis.CoRoots.Order6SporadicSection27F9G1
import SemigroupBasis.CoRoots.S5_870GapBlocks

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

/-! ## Literal Lee--Zhang beta forms -/

/-- A sparse gap contains no later occurrence, or one letter already
available at that first-occurrence block. -/
def ChoiceIn (allowed seconds : List Nat) : Prop :=
  seconds = [] ∨
    ∃ selected, selected ∈ allowed ∧ seconds = [selected]

/-- Proposition 27.3 condition (I), phrased over first-occurrence gap
blocks.  Unlike the Section 14 clean-block predicate, the current marker is
an allowed choice. -/
inductive SparseBlocks :
    List Nat → List FirstOccurrenceGapBlock → Prop
  | nil (seen : List Nat) : SparseBlocks seen []
  | cons (seen : List Nat) (block : FirstOccurrenceGapBlock)
      (rest : List FirstOccurrenceGapBlock)
      (markerFresh : block.marker ∉ seen)
      (choice : ChoiceIn (block.marker :: seen) block.seconds)
      (tail : SparseBlocks (block.marker :: seen) rest) :
      SparseBlocks seen (block :: rest)

namespace SparseBlocks

theorem wellFormed
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen blocks) :
    GapBlocksWellFormed seen blocks := by
  induction sparse with
  | nil seen =>
      exact GapBlocksWellFormed.nil seen
  | cons seen block rest markerFresh choice tail induction =>
      apply GapBlocksWellFormed.cons seen block rest markerFresh
      · intro letter member
        rcases choice with empty | ⟨selected, selectedSeen, shape⟩
        · simp [empty] at member
        · rw [shape] at member
          simp only [List.mem_singleton] at member
          subst letter
          exact selectedSeen
      · exact induction

theorem markersNodup
    {seen : List Nat} {blocks : List FirstOccurrenceGapBlock}
    (sparse : SparseBlocks seen blocks) :
    (gapBlockMarkers blocks).Nodup :=
  sparse.wellFormed.markersNodup

end SparseBlocks

/-- `left` occurs before `right` in the pinned first-occurrence order.
This is deliberately independent of the numeric variable names. -/
def EarlierIn (markers : List Nat) (left right : Nat) : Prop :=
  ∃ before middle after,
    markers = before ++ left :: middle ++ right :: after

/-- Proposition 27.3 condition (II) fails: the displayed word contains a
literal crossing `x_j ... x_k ... x_j ... x_k`, where `j < k` refers to
first-occurrence order. -/
def Has27Crossing (markers letters : List Nat) : Prop :=
  ∃ left right before firstGap secondGap thirdGap after,
    EarlierIn markers left right ∧
      letters =
        before ++ [left] ++ firstGap ++ [right] ++ secondGap ++
          [left] ++ thirdGap ++ [right] ++ after

/-- Proposition 27.3 condition (III) fails.  The adjacency between the
second `x_j` and the first `x_k` is literal; there is no omitted gap at that
boundary. -/
def Has27AdjacentPair (markers letters : List Nat) : Prop :=
  ∃ left right before firstGap secondGap after,
    EarlierIn markers left right ∧
      letters =
        before ++ [left] ++ firstGap ++ [left, right] ++
          secondGap ++ [right] ++ after

/-- The exact three Lee--Zhang beta-form clauses for a rendered block list. -/
structure BetaCanonicalBlocks
    (blocks : List FirstOccurrenceGapBlock) : Prop where
  sparse : SparseBlocks [] blocks
  noCrossing :
    ¬ Has27Crossing (gapBlockMarkers blocks) (renderGapBlocks blocks)
  noAdjacentPair :
    ¬ Has27AdjacentPair (gapBlockMarkers blocks) (renderGapBlocks blocks)

def BetaCanonicalList (letters : List Nat) : Prop :=
  BetaCanonicalBlocks (gapBlocksList letters)

/-! ## Shared finite separator contract -/

/-- The six finite values used by the least-differing-block argument in
Proposition 27.3.  Both F9 and G1 implement this same contract. -/
structure BetaSeparator (candidate : Semigroup (Fin 6)) where
  ordinary : Fin 6
  active : Fin 6
  bridge : Fin 6
  fresh : Fin 6
  hit : Fin 6
  miss : Fin 6
  hit_ne_miss : hit ≠ miss
  ordinary_active : candidate.mul ordinary active = active
  active_active : candidate.mul active active = hit
  active_ordinary : candidate.mul active ordinary = hit
  active_bridge : candidate.mul active bridge = active
  active_fresh : candidate.mul active fresh = miss
  fresh_absorbs : ∀ value, candidate.mul fresh value = fresh
  hit_absorbs : ∀ value, candidate.mul hit value = hit
  miss_absorbs : ∀ value, candidate.mul miss value = miss

namespace BetaSeparator

theorem eval_of_head_fresh
    {candidate : Semigroup (Fin 6)}
    (separator : BetaSeparator candidate)
    (valuation : Nat → Fin 6) (word : Word Nat)
    (atHead : valuation word.head = separator.fresh) :
    candidate.eval valuation word = separator.fresh := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [atHead]
      induction tail with
      | nil => rfl
      | cons letter rest induction =>
          simp only [List.foldl_cons]
          rw [separator.fresh_absorbs]
          exact induction atHead

theorem eval_kill_vs_empty
    {candidate : Semigroup (Fin 6)}
    (separator : BetaSeparator candidate)
    (valuation : Nat → Fin 6)
    (prefixWord leftTail rightTail : Word Nat) (killed : Nat)
    (prefixActive :
      candidate.eval valuation prefixWord = separator.active)
    (killedValue :
      valuation killed = separator.active ∨
        valuation killed = separator.ordinary)
    (leftFresh : valuation leftTail.head = separator.fresh)
    (rightFresh : valuation rightTail.head = separator.fresh) :
    candidate.eval valuation
          ((prefixWord ++ Word.singleton killed) ++ leftTail) =
        separator.hit ∧
      candidate.eval valuation (prefixWord ++ rightTail) =
        separator.miss := by
  have leftTailValue :=
    separator.eval_of_head_fresh valuation leftTail leftFresh
  have rightTailValue :=
    separator.eval_of_head_fresh valuation rightTail rightFresh
  constructor
  · simp only [Semigroup.eval_append, Semigroup.eval_singleton]
    rw [prefixActive, leftTailValue]
    rcases killedValue with active | ordinary
    · rw [active, separator.active_active, separator.hit_absorbs]
    · rw [ordinary, separator.active_ordinary, separator.hit_absorbs]
  · rw [Semigroup.eval_append, prefixActive, rightTailValue,
      separator.active_fresh]

theorem eval_kill_vs_bridge
    {candidate : Semigroup (Fin 6)}
    (separator : BetaSeparator candidate)
    (valuation : Nat → Fin 6)
    (prefixWord leftTail rightTail : Word Nat)
    (killed preserved : Nat)
    (prefixActive :
      candidate.eval valuation prefixWord = separator.active)
    (killedValue :
      valuation killed = separator.active ∨
        valuation killed = separator.ordinary)
    (preservedValue : valuation preserved = separator.bridge)
    (leftFresh : valuation leftTail.head = separator.fresh)
    (rightFresh : valuation rightTail.head = separator.fresh) :
    candidate.eval valuation
          ((prefixWord ++ Word.singleton killed) ++ leftTail) =
        separator.hit ∧
      candidate.eval valuation
          ((prefixWord ++ Word.singleton preserved) ++ rightTail) =
        separator.miss := by
  have leftTailValue :=
    separator.eval_of_head_fresh valuation leftTail leftFresh
  have rightTailValue :=
    separator.eval_of_head_fresh valuation rightTail rightFresh
  constructor
  · simp only [Semigroup.eval_append, Semigroup.eval_singleton]
    rw [prefixActive, leftTailValue]
    rcases killedValue with active | ordinary
    · rw [active, separator.active_active, separator.hit_absorbs]
    · rw [ordinary, separator.active_ordinary, separator.hit_absorbs]
  · simp only [Semigroup.eval_append, Semigroup.eval_singleton]
    rw [prefixActive, preservedValue, separator.active_bridge,
      rightTailValue, separator.active_fresh]

end BetaSeparator

end SemigroupBasis.CoRoots.Order6SporadicSection27

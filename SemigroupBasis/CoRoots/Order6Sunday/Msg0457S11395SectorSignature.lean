import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395CoordinateSectors

/-! Reduced sector coordinates are canonically determined by their parity
vectors and suffix-support flags. Actual Chain profiles satisfy the required
bounds. Translating word signatures and the actual resolver into this scalar
statement remains explicit work, not an assumed completeness field. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorSignature

open SemigroupBasis
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395ResolveLetter
open Msg0457S11395CoordinateSectors

def suffixFlags : List (List Nat) → List Bool
  | [] => [false]
  | block :: rest => positive (block ++ rest.flatten) :: suffixFlags rest

def FutureBound : List (List Nat) → Prop
  | [] => True
  | block :: rest => (positive rest.flatten = true → ∀ count ∈ block, count ≤ 1) ∧ FutureBound rest

def canonicalBlocks (blocks : List (List Nat)) : List (List Nat) := blocks.map canonical

theorem suffixFlags_head (blocks : List (List Nat)) :
    (suffixFlags blocks).head? = some (positive blocks.flatten) := by
  cases blocks <;> rfl

theorem positive_eq_of_suffixFlags (left right : List (List Nat))
    (same : suffixFlags left = suffixFlags right) : positive left.flatten = positive right.flatten := by
  have heads := congrArg (fun flags : List Bool => flags.head?) same
  change (suffixFlags left).head? = (suffixFlags right).head? at heads
  rw [suffixFlags_head, suffixFlags_head] at heads
  exact Option.some.inj heads

/-- Before a future occupied sector there is no pair ambiguity; in the last
occupied sector support decides whether an all-even profile needs a pair. -/
theorem canonicalBlocks_eq (left right : List (List Nat))
    (leftBound : FutureBound left) (rightBound : FutureBound right)
    (sameBits : left.map bits = right.map bits) (sameFlags : suffixFlags left = suffixFlags right) :
    canonicalBlocks left = canonicalBlocks right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons block rest => simp at sameBits
  | cons leftBlock leftRest ih =>
      cases right with
      | nil => simp at sameBits
      | cons rightBlock rightRest =>
          have bitParts := List.cons.inj sameBits
          have flagParts := List.cons.inj sameFlags
          have futureEqual := positive_eq_of_suffixFlags leftRest rightRest flagParts.2
          have headEqual : canonical leftBlock = canonical rightBlock := by
            cases active : positive leftRest.flatten with
            | true =>
                have rightActive := futureEqual.symm.trans active
                exact (canonical_of_small leftBlock (leftBound.1 active)).trans
                  (bitParts.1.trans (canonical_of_small rightBlock (rightBound.1 rightActive)).symm)
            | false =>
                have rightEmpty := futureEqual.symm.trans active
                have headSupport : positive leftBlock = positive rightBlock := by
                  have full := flagParts.1
                  change positive (leftBlock ++ leftRest.flatten) = positive (rightBlock ++ rightRest.flatten) at full
                  simpa only [positive_append, active, rightEmpty, Bool.or_false] using full
                exact canonical_eq_of_observations leftBlock rightBlock bitParts.1 headSupport
          change canonical leftBlock :: canonicalBlocks leftRest = canonical rightBlock :: canonicalBlocks rightRest
          rw [headEqual, ih rightRest leftBound.2 rightBound.2 bitParts.2 flagParts.2]

theorem reducedCounts_suffix (before after : List Nat) (red : ReducedCounts (before ++ after)) :
    ReducedCounts after := by
  induction before with
  | nil => exact red
  | cons count rest ih => exact ih red.2

theorem reducedCounts_prefix (before after : List Nat) (red : ReducedCounts (before ++ after)) :
    ReducedCounts before := by
  induction before with
  | nil => trivial
  | cons count rest ih =>
      refine ⟨?_, ih red.2⟩
      cases active : positive rest with
      | true =>
          have future : positive (rest ++ after) = true := by rw [positive_append, active]; rfl
          have bound : count ≤ (if positive (rest ++ after) then 1 else 2) := red.1
          rw [future] at bound
          exact bound
      | false =>
          have cap : (if positive (rest ++ after) then 1 else 2) ≤ 2 := by split <;> omega
          exact Nat.le_trans red.1 cap

theorem reducedCounts_prefix_before_future (before after : List Nat)
    (red : ReducedCounts (before ++ after)) (future : positive after = true) :
    ∀ count ∈ before, count ≤ 1 := by
  induction before with
  | nil => simp
  | cons first rest ih =>
      have later : positive (rest ++ after) = true := by simp only [positive_append, future, Bool.or_true]
      have headBound : first ≤ 1 := by
        have bound : first ≤ (if positive (rest ++ after) then 1 else 2) := red.1
        rw [later] at bound
        exact bound
      intro count member
      rcases List.mem_cons.mp member with equal | tail
      · simpa [equal] using headBound
      · exact ih red.2 count tail

theorem futureBound_of_reduced (blocks : List (List Nat)) (red : ReducedCounts blocks.flatten) :
    FutureBound blocks := by
  induction blocks with
  | nil => trivial
  | cons block rest ih =>
      exact ⟨fun future => reducedCounts_prefix_before_future block rest.flatten red future,
        ih (reducedCounts_suffix block rest.flatten red)⟩

theorem resolveBlocks_eq_canonical (blocks : List (List Nat)) (red : ReducedCounts blocks.flatten) :
    blocks.map (Msg0457S11395CoordinateSectors.resolve false) = canonicalBlocks blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      change Msg0457S11395CoordinateSectors.resolve false block ::
          rest.map (Msg0457S11395CoordinateSectors.resolve false) = canonical block :: canonicalBlocks rest
      rw [resolve_false_eq block (reducedCounts_prefix block rest.flatten red),
        ih (reducedCounts_suffix block rest.flatten red)]

theorem positive_profile_mem (chain : Chain) (tested : Nat)
    (active : positive (gapProfile tested chain) = true) : tested ∈ flatten chain := by
  induction chain with
  | stop gap =>
      have countPositive : 0 < gap.count tested := by simpa [gapProfile, positive] using active
      exact List.count_pos_iff.mp countPositive
  | step gap fresh tail ih =>
      by_cases present : 0 < gap.count tested
      · exact List.mem_append_left _ (List.count_pos_iff.mp present)
      · have tailActive : positive (gapProfile tested tail) = true := by
          simpa [gapProfile, positive, present] using active
        exact List.mem_append_right gap (List.mem_cons_of_mem fresh (ih tailActive))

theorem gapProfile_reduced (chain : Chain) (red : Reduced chain) (tested : Nat) :
    ReducedCounts (gapProfile tested chain) := by
  induction chain with
  | stop gap => exact ⟨by simpa using red tested, trivial⟩
  | step gap fresh tail ih =>
      refine ⟨?_, ih red.2⟩
      cases active : positive (gapProfile tested tail) with
      | true =>
          have later : tested ∈ fresh :: flatten tail := List.mem_cons_of_mem fresh (positive_profile_mem tail tested active)
          simpa only [if_pos later] using red.1 tested
      | false =>
          have cap : (if tested ∈ fresh :: flatten tail then 1 else 2) ≤ 2 := by split <;> omega
          exact Nat.le_trans (red.1 tested) cap

def prependSectorCell (count : Nat) (cut : Bool) : List (List Nat) → List (List Nat)
  | [] => [[count]]
  | block :: rest => if cut then [count] :: block :: rest else (count :: block) :: rest

theorem flatten_prependSectorCell (count : Nat) (cut : Bool) (blocks : List (List Nat)) :
    (prependSectorCell count cut blocks).flatten = count :: blocks.flatten := by
  cases blocks with
  | nil => rfl
  | cons block rest => cases cut <;> rfl

/-- Actual simple-marker sectors, read from the original whole-word counts. -/
def sectorCounts (whole : List Nat) (tested : Nat) : Chain → List (List Nat)
  | .stop gap => [[gap.count tested]]
  | .step gap fresh tail =>
      prependSectorCell (gap.count tested) (decide (whole.count fresh = 1)) (sectorCounts whole tested tail)

theorem sectorCounts_flatten (whole : List Nat) (tested : Nat) (chain : Chain) :
    (sectorCounts whole tested chain).flatten = gapProfile tested chain := by
  induction chain with
  | stop gap => rfl
  | step gap fresh tail ih => rw [sectorCounts, flatten_prependSectorCell, ih]; rfl

theorem sectorCounts_reduced (whole : List Nat) (tested : Nat) (chain : Chain) (red : Reduced chain) :
    ReducedCounts (sectorCounts whole tested chain).flatten := by
  rw [sectorCounts_flatten]
  exact gapProfile_reduced chain red tested

theorem sectorCounts_futureBound (whole : List Nat) (tested : Nat) (chain : Chain) (red : Reduced chain) :
    FutureBound (sectorCounts whole tested chain) :=
  futureBound_of_reduced _ (sectorCounts_reduced whole tested chain red)

theorem actual_sector_scalar_resolution (whole : List Nat) (tested : Nat) (chain : Chain) (red : Reduced chain) :
    (sectorCounts whole tested chain).map (Msg0457S11395CoordinateSectors.resolve false) =
      canonicalBlocks (sectorCounts whole tested chain) :=
  resolveBlocks_eq_canonical _ (sectorCounts_reduced whole tested chain red)

theorem actual_sector_canonical_comparison (leftWhole rightWhole : List Nat) (tested : Nat) (left right : Chain)
    (leftRed : Reduced left) (rightRed : Reduced right)
    (sameBits : (sectorCounts leftWhole tested left).map bits = (sectorCounts rightWhole tested right).map bits)
    (sameFlags : suffixFlags (sectorCounts leftWhole tested left) = suffixFlags (sectorCounts rightWhole tested right)) :
    canonicalBlocks (sectorCounts leftWhole tested left) = canonicalBlocks (sectorCounts rightWhole tested right) :=
  canonicalBlocks_eq _ _ (sectorCounts_futureBound leftWhole tested left leftRed)
    (sectorCounts_futureBound rightWhole tested right rightRed) sameBits sameFlags

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SectorSignature

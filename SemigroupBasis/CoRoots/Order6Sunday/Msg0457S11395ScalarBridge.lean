import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ScalarRender

/-! The actual Chain resolver's numeric trace is scalar resolution on
its actual simple-marker sectors. This closes the algorithm-to-scalar
bridge; recovering scalar observations from SameSignature is separate. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ScalarBridge

open SemigroupBasis
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395PairResolver
open Msg0457S11395ResolveLetter Msg0457S11395CoordinateSectors
open Msg0457S11395SectorSignature Msg0457S11395ResolverProjection
open Msg0457S11395ResolverState Msg0457S11395ScalarRender

theorem scalarRender_pair_chain (whole : List Nat) (past : Bool) (letter : Nat) (chain : Chain)
    (red : Reduced chain) (pair : 2 ≤ (headGap chain).count letter) :
    scalarRender past (sectorCounts whole letter chain) =
      if past then zeroProfile chain else pairVector whole chain := by
  obtain ⟨block,rest,shape⟩ := sectorCounts_head_shape whole letter chain
  have profileShape : gapProfile letter chain = (headGap chain).count letter :: (block ++ rest.flatten) := by
    rw [← sectorCounts_flatten whole letter chain, shape]
    rfl
  have reducedProfile := gapProfile_reduced chain red letter
  rw [profileShape] at reducedProfile
  obtain ⟨two,tailZeros⟩ := reducedCounts_pair _ _ reducedProfile pair
  have restZeros : ∀ count ∈ rest.flatten, count = 0 := fun count member =>
    tailZeros count (List.mem_append_right _ member)
  have lengths : (introductions chain).length + 1 = (block ++ rest.flatten).length + 1 := by
    have lengths := gapProfile_length letter chain
    rw [profileShape, List.length_cons] at lengths
    exact lengths.symm
  have zeroVector : zeroProfile chain = 0 :: (block ++ rest.flatten) := by
    rw [zeroProfile, lengths, List.replicate_succ]
    exact congrArg (List.cons 0) (all_zero_replicate (block ++ rest.flatten) tailZeros).symm
  have paired : pairVector whole chain =
      endPair (block.length + 1) ++ List.replicate rest.flatten.length 0 := by
    rw [pairVector_eq_pairBlocks whole letter chain, shape, two]
    rfl
  rw [shape, two, scalarRender_pair past block rest restZeros]
  cases past with
  | false =>
      exact (congrArg (List.append (endPair (block.length + 1)))
        (all_zero_replicate rest.flatten restZeros)).trans paired.symm
  | true => exact zeroVector.symm

theorem numeric_eq_scalarRender (whole : List Nat) (past : Bool) (letter : Nat) (chain : Chain)
    (red : Reduced chain) :
    numeric whole past letter chain = scalarRender past (sectorCounts whole letter chain) := by
  induction chain generalizing past with
  | stop gap =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa only [numeric, if_pos pair] using
          (scalarRender_pair_chain whole past letter (.stop gap) red pair).symm
      · simp [numeric, sectorCounts, scalarRender, resolve, pair]
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa only [numeric, if_pos pair] using
          (scalarRender_pair_chain whole past letter (.step gap fresh tail) red pair).symm
      · rw [numeric, if_neg pair, sectorCounts,
          scalarRender_prepend_small past (decide (whole.count fresh = 1)) (gap.count letter) _ pair]
        have flag : (if decide (whole.count fresh = 1) then false else past || decide (0 < gap.count letter)) =
            (if whole.count fresh = 1 then false else past || decide (0 < gap.count letter)) := by
          by_cases cut : whole.count fresh = 1 <;> simp [cut]
        rw [flag]
        exact congrArg (List.cons (gap.count letter)) (ih _ red.2)

theorem scalarRender_false_canonical (whole : List Nat) (letter : Nat) (chain : Chain)
    (red : Reduced chain) :
    scalarRender false (sectorCounts whole letter chain) =
      (canonicalBlocks (sectorCounts whole letter chain)).flatten := by
  rw [scalarRender_false, actual_sector_scalar_resolution whole letter chain red]

theorem numeric_false_canonical (whole : List Nat) (letter : Nat) (chain : Chain)
    (red : Reduced chain) :
    numeric whole false letter chain = (canonicalBlocks (sectorCounts whole letter chain)).flatten :=
  (numeric_eq_scalarRender whole false letter chain red).trans
    (scalarRender_false_canonical whole letter chain red)

theorem resolveLetter_profile_scalar (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (red : Reduced chain) :
    gapProfile letter (resolveLetter prefixWords letter chain) =
      scalarRender (available (prefixWords ++ flatten chain) prefixWords letter)
        (sectorCounts (prefixWords ++ flatten chain) letter chain) :=
  (resolveLetter_profile_numeric prefixWords letter chain good red).trans
    (numeric_eq_scalarRender _ _ letter chain red)

theorem singleton_resolver_canonical (head letter : Nat) (chain : Chain)
    (good : WellFormed [head] chain) (red : Reduced chain) :
    gapProfile letter (resolveLetter [head] letter chain) =
      (canonicalBlocks (sectorCounts ([head] ++ flatten chain) letter chain)).flatten :=
  (singleton_resolver_profile head letter chain good red).trans
    (numeric_false_canonical _ letter chain red)

/-- The conclusion compares the actual resolver outputs. Its only remaining
observation hypotheses are the scalar parity vectors and suffix flags. -/
theorem singleton_resolver_eq_of_observations (leftHead rightHead letter : Nat) (left right : Chain)
    (leftGood : WellFormed [leftHead] left) (rightGood : WellFormed [rightHead] right)
    (leftRed : Reduced left) (rightRed : Reduced right)
    (sameBits : (sectorCounts ([leftHead] ++ flatten left) letter left).map bits =
      (sectorCounts ([rightHead] ++ flatten right) letter right).map bits)
    (sameFlags : suffixFlags (sectorCounts ([leftHead] ++ flatten left) letter left) =
      suffixFlags (sectorCounts ([rightHead] ++ flatten right) letter right)) :
    gapProfile letter (resolveLetter [leftHead] letter left) =
      gapProfile letter (resolveLetter [rightHead] letter right) := by
  rw [singleton_resolver_canonical leftHead letter left leftGood leftRed,
    singleton_resolver_canonical rightHead letter right rightGood rightRed]
  exact congrArg List.flatten
    (actual_sector_canonical_comparison _ _ letter left right leftRed rightRed sameBits sameFlags)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ScalarBridge

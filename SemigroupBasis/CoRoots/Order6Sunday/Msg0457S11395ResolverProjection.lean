import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolverState

/-! Exact numeric projection of the existing Chain resolver. The selector
state and the endpoint both refer to the original whole word. No new
normalizer is substituted for resolveLetter. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolverProjection

open SemigroupBasis
open Msg0457S11395WordGaps Msg0457S11395WordReduction Msg0457S11395SectorEndpoint
open Msg0457S11395PairResolver Msg0457S11395ResolveLetter Msg0457S11395SectorCut
open Msg0457S11395ResolverState

def zeroProfile (chain : Chain) : List Nat :=
  List.replicate ((introductions chain).length + 1) 0

def pairVector (whole : List Nat) : Chain → List Nat
  | .stop _ => [2]
  | .step _ fresh tail =>
      if whole.count fresh = 1 then 2 :: zeroProfile tail
      else 0 :: pairVector whole tail

theorem zeroProfile_dropPair (letter : Nat) (chain : Chain) :
    zeroProfile (dropPair letter chain) = zeroProfile chain := by
  simp only [zeroProfile, dropPair_introductions]

theorem pairVector_dropPair (whole : List Nat) (letter : Nat) (chain : Chain) :
    pairVector whole (dropPair letter chain) = pairVector whole chain := by
  cases chain <;> rfl

theorem pairVector_congr_counts (left right : List Nat) (chain : Chain)
    (same : ∀ tested, left.count tested = right.count tested) :
    pairVector left chain = pairVector right chain := by
  induction chain with
  | stop gap => rfl
  | step gap fresh tail ih => simp only [pairVector, same fresh, ih]

theorem gapProfile_zero (letter : Nat) (chain : Chain) (absent : letter ∉ flatten chain) :
    gapProfile letter chain = zeroProfile chain := by
  induction chain with
  | stop gap =>
      have zero : gap.count letter = 0 := List.count_eq_zero.mpr absent
      simpa only [gapProfile, zeroProfile, introductions, List.length_nil, Nat.zero_add, List.replicate_succ,
        List.replicate_zero] using congrArg (fun n => [n]) zero
  | step gap fresh tail ih =>
      have missingGap : letter ∉ gap := fun member => absent (List.mem_append_left _ member)
      have missingTail : letter ∉ flatten tail := fun member =>
        absent (List.mem_append_right gap (List.mem_cons_of_mem fresh member))
      change gap.count letter :: gapProfile letter tail = 0 :: zeroProfile tail
      rw [List.count_eq_zero.mpr missingGap, ih missingTail]

/-- A missing letter's pair is placed precisely at the end of the first
simple-marker sector, using source counts that include the selected pair. -/
theorem pushPair_profile_zero (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (absent : letter ∉ flatten chain) :
    gapProfile letter (pushPair letter chain) =
      pairVector (prefixWords ++ [letter,letter] ++ flatten chain) chain := by
  induction chain generalizing prefixWords with
  | stop gap =>
      have zero : gap.count letter = 0 := List.count_eq_zero.mpr absent
      simp [pushPair, gapProfile, pairVector, List.count_append, zero]
  | step gap fresh tail ih =>
      have missingGap : letter ∉ gap := fun member => absent (List.mem_append_left _ member)
      have missingTail : letter ∉ flatten tail := fun member =>
        absent (List.mem_append_right gap (List.mem_cons_of_mem fresh member))
      have zero : gap.count letter = 0 := List.count_eq_zero.mpr missingGap
      have markerCount : (prefixWords ++ [letter,letter] ++ flatten (.step gap fresh tail)).count fresh =
          (prefixWords ++ flatten (.step gap fresh tail)).count fresh :=
        pair_source_count prefixWords (.step gap fresh tail) letter fresh absent
          (List.mem_append_right gap (List.mem_cons_self))
      by_cases repeated : fresh ∈ flatten tail
      · have notSimple : (prefixWords ++ [letter,letter] ++ flatten (.step gap fresh tail)).count fresh ≠ 1 := by
          rw [markerCount]
          intro simple
          exact ((fresh_simple_iff prefixWords gap fresh tail good).1 simple) repeated
        have tailStep := ih (prefixWords ++ gap ++ [fresh]) good.2.2 missingTail
        have sameVector : pairVector ((prefixWords ++ gap ++ [fresh]) ++ [letter,letter] ++ flatten tail) tail =
            pairVector (prefixWords ++ [letter,letter] ++ flatten (.step gap fresh tail)) tail := by
          apply pairVector_congr_counts
          intro tested
          simp only [flatten, List.count_append, List.count_cons, List.count_nil]
          omega
        simp only [pushPair, if_pos repeated, gapProfile, pairVector, if_neg notSimple]
        rw [zero, tailStep, sameVector]
      · have simple : (prefixWords ++ [letter,letter] ++ flatten (.step gap fresh tail)).count fresh = 1 := by
          rw [markerCount]
          exact (fresh_simple_iff prefixWords gap fresh tail good).2 repeated
        simp only [pushPair, if_neg repeated, gapProfile, pairVector, if_pos simple]
        rw [List.count_append, zero, gapProfile_zero letter tail missingTail]
        simp

theorem resolveHead_profile (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (red : Reduced chain)
    (pair : 2 ≤ (headGap chain).count letter) :
    gapProfile letter (resolveHead prefixWords letter chain) =
      if available (prefixWords ++ flatten chain) prefixWords letter then zeroProfile chain
      else pairVector (prefixWords ++ flatten chain) chain := by
  have missing := dropPair_final letter chain red pair
  have dropped : gapProfile letter (dropPair letter chain) = zeroProfile chain :=
    (gapProfile_zero letter _ missing).trans (zeroProfile_dropPair letter chain)
  have placed : gapProfile letter (pushPair letter (dropPair letter chain)) =
      pairVector (prefixWords ++ flatten chain) chain := by
    have actual := pushPair_profile_zero prefixWords letter (dropPair letter chain)
      (dropPair_wellFormed prefixWords letter chain good pair) missing
    have same : pairVector (prefixWords ++ [letter,letter] ++ flatten (dropPair letter chain)) (dropPair letter chain) =
        pairVector (prefixWords ++ flatten chain) (dropPair letter chain) := by
      apply pairVector_congr_counts
      intro tested
      have count := dropPair_counts letter tested chain pair
      simp only [List.count_append]
      omega
    exact actual.trans (same.trans (pairVector_dropPair _ letter chain))
  cases found : Msg0457S11395Absorber.find (prefixWords ++ flatten chain) prefixWords letter with
  | none => simpa [resolveHead, available, found] using placed
  | some parts => simpa [resolveHead, available, found] using dropped

/-- Numeric trace on the literal gap coordinates and source simple markers.
This is a projection target, not a replacement word normalizer. -/
def numeric (whole : List Nat) (past : Bool) (letter : Nat) : Chain → List Nat
  | .stop gap =>
      if 2 ≤ gap.count letter then
        if past then zeroProfile (.stop gap) else pairVector whole (.stop gap)
      else [gap.count letter]
  | .step gap fresh tail =>
      if 2 ≤ gap.count letter then
        if past then zeroProfile (.step gap fresh tail) else pairVector whole (.step gap fresh tail)
      else gap.count letter :: numeric whole
        (if whole.count fresh = 1 then false else past || decide (0 < gap.count letter)) letter tail

theorem resolveLetter_profile_numeric (prefixWords : List Nat) (letter : Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) (red : Reduced chain) :
    gapProfile letter (resolveLetter prefixWords letter chain) =
      numeric (prefixWords ++ flatten chain)
        (available (prefixWords ++ flatten chain) prefixWords letter) letter chain := by
  induction chain generalizing prefixWords with
  | stop gap =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa only [resolveLetter, numeric, if_pos pair] using
          resolveHead_profile prefixWords letter (.stop gap) good red pair
      · simp [resolveLetter, numeric, pair, gapProfile]
  | step gap fresh tail ih =>
      by_cases pair : 2 ≤ gap.count letter
      · simpa only [resolveLetter, numeric, if_pos pair] using
          resolveHead_profile prefixWords letter (.step gap fresh tail) good red pair
      · have smaller := ih (prefixWords ++ gap ++ [fresh]) good.2.2 red.2
        have wholeSame : (prefixWords ++ gap ++ [fresh]) ++ flatten tail =
            prefixWords ++ flatten (.step gap fresh tail) := by
          simp [flatten, List.append_assoc]
        rw [wholeSame, actual_step_available prefixWords gap letter fresh tail good] at smaller
        simp only [resolveLetter, numeric, if_neg pair, gapProfile]
        exact congrArg (List.cons (gap.count letter)) smaller

theorem singleton_resolver_profile (head letter : Nat) (chain : Chain)
    (good : WellFormed [head] chain) (red : Reduced chain) :
    gapProfile letter (resolveLetter [head] letter chain) =
      numeric ([head] ++ flatten chain) false letter chain := by
  simpa only [available_singleton] using resolveLetter_profile_numeric [head] letter chain good red

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ResolverProjection

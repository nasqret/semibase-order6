import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProfileSupport

/-! The actual sector suffix flags are the initial gap support followed
by gap supports immediately after simple introductions and terminal false.
Literal SameSignature supplies every one of these observations. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SuffixFlags

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0457S11395WordGaps Msg0457S11395ResolveLetter Msg0457S11395Observations
open Msg0457S11395CoordinateSectors Msg0457S11395SectorSignature Msg0457S11395ScalarRender
open Msg0457S11395Suffix Msg0457S11395IntroductionOrder Msg0457S11395ProfileSupport

def cutFlags (whole : List Nat) (tested : Nat) : Chain → List Bool
  | .stop _ => [false]
  | .step _ fresh tail =>
      if whole.count fresh = 1 then positive (gapProfile tested tail) :: cutFlags whole tested tail
      else cutFlags whole tested tail

theorem suffixFlags_prepend (count : Nat) (cut : Bool) (blocks : List (List Nat)) (nonempty : blocks ≠ []) :
    suffixFlags (prependSectorCell count cut blocks) =
      positive (count :: blocks.flatten) :: (if cut then suffixFlags blocks else (suffixFlags blocks).tail) := by
  cases blocks with
  | nil => exact False.elim (nonempty rfl)
  | cons block rest => cases cut <;> rfl

theorem sectorCounts_nonempty (whole : List Nat) (tested : Nat) (chain : Chain) :
    sectorCounts whole tested chain ≠ [] := by
  obtain ⟨block,rest,shape⟩ := sectorCounts_head_shape whole tested chain
  rw [shape]
  exact List.cons_ne_nil _ _

theorem suffixFlags_eq_cutFlags (whole : List Nat) (tested : Nat) (chain : Chain) :
    suffixFlags (sectorCounts whole tested chain) = positive (gapProfile tested chain) :: cutFlags whole tested chain := by
  induction chain with
  | stop gap => rfl
  | step gap fresh tail ih =>
      rw [sectorCounts, suffixFlags_prepend _ _ _ (sectorCounts_nonempty whole tested tail),
        sectorCounts_flatten, ih]
      by_cases cut : whole.count fresh = 1 <;> simp [cutFlags, cut, gapProfile]

theorem suffixAfter_step (prefixWords gap : List Nat) (fresh : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail)) :
    suffixAfter fresh (prefixWords ++ flatten (.step gap fresh tail)) = flatten tail := by
  change suffixAfter fresh (prefixWords ++ (gap ++ fresh :: flatten tail)) = _
  rw [← List.append_assoc]
  exact suffixAfter_split fresh (prefixWords ++ gap) (flatten tail)
    (fresh_absent_before prefixWords gap fresh good.1 good.2.1)

theorem signature_repeated {left right : Word Nat} (same : SameSignature left right) (tested : Nat) :
    2 ≤ left.toList.count tested ↔ 2 ≤ right.toList.count tested := by
  have capped := ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts tested)).1
  omega

theorem signature_step_tail_positive (leftWord rightWord : Word Nat) (same : SameSignature leftWord rightWord)
    (leftPrefix rightPrefix leftGap rightGap : List Nat) (fresh tested : Nat) (leftTail rightTail : Chain)
    (leftGood : WellFormed leftPrefix (.step leftGap fresh leftTail))
    (rightGood : WellFormed rightPrefix (.step rightGap fresh rightTail))
    (leftShape : leftWord.toList = leftPrefix ++ flatten (.step leftGap fresh leftTail))
    (rightShape : rightWord.toList = rightPrefix ++ flatten (.step rightGap fresh rightTail))
    (simple : S5_254.GloballySimple leftWord fresh) :
    positive (gapProfile tested leftTail) = positive (gapProfile tested rightTail) := by
  have rightSimple := (same.simple fresh).mp simple
  have leftSuffix : suffixAfter fresh leftWord.toList = flatten leftTail := by
    rw [leftShape]
    exact suffixAfter_step leftPrefix leftGap fresh leftTail leftGood
  have rightSuffix : suffixAfter fresh rightWord.toList = flatten rightTail := by
    rw [rightShape]
    exact suffixAfter_step rightPrefix rightGap fresh rightTail rightGood
  have suffixSupport := same.suffixSupport fresh simple rightSimple tested
  rw [leftSuffix, rightSuffix] at suffixSupport
  have leftTailShape : leftWord.toList = (leftPrefix ++ leftGap ++ [fresh]) ++ flatten leftTail := by
    simpa only [flatten, List.append_assoc, List.singleton_append] using leftShape
  have rightTailShape : rightWord.toList = (rightPrefix ++ rightGap ++ [fresh]) ++ flatten rightTail := by
    simpa only [flatten, List.append_assoc, List.singleton_append] using rightShape
  rw [profile_positive_formula _ leftTail tested leftGood.2.2,
    profile_positive_formula _ rightTail tested rightGood.2.2, ← leftTailShape, ← rightTailShape]
  simp only [signature_repeated same tested, suffixSupport]

theorem signature_cutFlags (leftWord rightWord : Word Nat) (same : SameSignature leftWord rightWord)
    (tested : Nat) (left right : Chain) (leftPrefix rightPrefix : List Nat)
    (leftGood : WellFormed leftPrefix left) (rightGood : WellFormed rightPrefix right)
    (leftShape : leftWord.toList = leftPrefix ++ flatten left)
    (rightShape : rightWord.toList = rightPrefix ++ flatten right)
    (sameIntroductions : introductions left = introductions right) :
    cutFlags leftWord.toList tested left = cutFlags rightWord.toList tested right := by
  induction left generalizing right leftPrefix rightPrefix with
  | stop leftGap =>
      cases right with
      | stop rightGap => rfl
      | step rightGap fresh tail => simp [introductions] at sameIntroductions
  | step leftGap fresh leftTail ih =>
      cases right with
      | stop rightGap => simp [introductions] at sameIntroductions
      | step rightGap nextFresh rightTail =>
          have markers := List.cons.inj sameIntroductions
          have equalFresh : fresh = nextFresh := markers.1
          subst nextFresh
          have leftTailShape : leftWord.toList = (leftPrefix ++ leftGap ++ [fresh]) ++ flatten leftTail := by
            simpa only [flatten, List.append_assoc, List.singleton_append] using leftShape
          have rightTailShape : rightWord.toList = (rightPrefix ++ rightGap ++ [fresh]) ++ flatten rightTail := by
            simpa only [flatten, List.append_assoc, List.singleton_append] using rightShape
          have tailEqual := ih rightTail (leftPrefix ++ leftGap ++ [fresh]) (rightPrefix ++ rightGap ++ [fresh])
            leftGood.2.2 rightGood.2.2 leftTailShape rightTailShape markers.2
          have simpleEqual : leftWord.toList.count fresh = 1 ↔ rightWord.toList.count fresh = 1 := same.simple fresh
          by_cases simple : leftWord.toList.count fresh = 1
          · have rightSimple := simpleEqual.mp simple
            have active := signature_step_tail_positive leftWord rightWord same leftPrefix rightPrefix
              leftGap rightGap fresh tested leftTail rightTail leftGood rightGood leftShape rightShape simple
            simp only [cutFlags, if_pos simple, if_pos rightSimple, active, tailEqual]
          · have rightNotSimple : ¬ rightWord.toList.count fresh = 1 := fun proof => simple (simpleEqual.mpr proof)
            simp only [cutFlags, if_neg simple, if_neg rightNotSimple, tailEqual]

theorem signature_suffixFlags (leftHead rightHead tested : Nat) (left right : Chain)
    (leftGood : WellFormed [leftHead] left) (rightGood : WellFormed [rightHead] right)
    (same : SameSignature ⟨leftHead,flatten left⟩ ⟨rightHead,flatten right⟩) :
    suffixFlags (sectorCounts (leftHead :: flatten left) tested left) =
      suffixFlags (sectorCounts (rightHead :: flatten right) tested right) := by
  rw [suffixFlags_eq_cutFlags, suffixFlags_eq_cutFlags,
    singleton_profile_positive leftHead tested left leftGood,
    singleton_profile_positive rightHead tested right rightGood]
  have repeatedEqual : (2 ≤ (leftHead :: flatten left).count tested) ↔
      (2 ≤ (rightHead :: flatten right).count tested) := signature_repeated same tested
  simp only [repeatedEqual]
  apply congrArg (List.cons (decide (2 ≤ (rightHead :: flatten right).count tested)))
  exact signature_cutFlags ⟨leftHead,flatten left⟩ ⟨rightHead,flatten right⟩ same tested left right
    [leftHead] [rightHead] leftGood rightGood rfl rfl
    (signature_heads_introductions leftHead rightHead left right leftGood rightGood same).2

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395SuffixFlags

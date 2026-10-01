import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395IntroductionOrder

/-! Equal literal first-prefix parities telescope to equal actual gap bits.
Equal simple-letter cuts then give the nested parity observation consumed
by the actual resolver comparison. No Reduced or bounded-word premise. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395GapParity

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0457S11395WordGaps Msg0457S11395ResolveLetter Msg0457S11395Observations
open Msg0457S11395CoordinateSectors Msg0457S11395SectorSignature
open Msg0457S11395IntroductionOrder

theorem gapBits_eq_of_prefixes (left right : Chain) (leftPrefix rightPrefix : List Nat) (tested : Nat)
    (leftGood : WellFormed leftPrefix left) (rightGood : WellFormed rightPrefix right)
    (sameIntroductions : introductions left = introductions right)
    (samePrefix : leftPrefix.count tested % 2 = rightPrefix.count tested % 2)
    (sameTotal : (leftPrefix ++ flatten left).count tested % 2 =
      (rightPrefix ++ flatten right).count tested % 2)
    (sameFirstPrefixes : ∀ fresh ∈ introductions left,
      (S5_254.simplePrefixBefore fresh (leftPrefix ++ flatten left)).count tested % 2 =
      (S5_254.simplePrefixBefore fresh (rightPrefix ++ flatten right)).count tested % 2) :
    bits (gapProfile tested left) = bits (gapProfile tested right) := by
  induction left generalizing right leftPrefix rightPrefix with
  | stop leftGap =>
      cases right with
      | stop rightGap =>
          have equal : leftGap.count tested % 2 = rightGap.count tested % 2 := by
            simp only [flatten, List.count_append] at sameTotal
            omega
          change [leftGap.count tested % 2] = [rightGap.count tested % 2]
          rw [equal]
      | step rightGap fresh tail => simp [introductions] at sameIntroductions
  | step leftGap fresh leftTail ih =>
      cases right with
      | stop rightGap => simp [introductions] at sameIntroductions
      | step rightGap nextFresh rightTail =>
          have markers := List.cons.inj sameIntroductions
          have equalFresh : fresh = nextFresh := markers.1
          subst nextFresh
          have atFresh := sameFirstPrefixes fresh (by simp [introductions])
          rw [firstPrefix_step leftPrefix leftGap fresh leftTail leftGood,
            firstPrefix_step rightPrefix rightGap fresh rightTail rightGood] at atFresh
          have equalGap : leftGap.count tested % 2 = rightGap.count tested % 2 := by
            simp only [List.count_append] at atFresh
            omega
          have extended : (leftPrefix ++ leftGap ++ [fresh]).count tested % 2 =
              (rightPrefix ++ rightGap ++ [fresh]).count tested % 2 := by
            simp only [List.count_append] at atFresh ⊢
            omega
          have tailTotal : ((leftPrefix ++ leftGap ++ [fresh]) ++ flatten leftTail).count tested % 2 =
              ((rightPrefix ++ rightGap ++ [fresh]) ++ flatten rightTail).count tested % 2 := by
            simpa only [flatten, List.append_assoc, List.singleton_append] using sameTotal
          have tailPrefixes : ∀ marker ∈ introductions leftTail,
              (S5_254.simplePrefixBefore marker
                ((leftPrefix ++ leftGap ++ [fresh]) ++ flatten leftTail)).count tested % 2 =
              (S5_254.simplePrefixBefore marker
                ((rightPrefix ++ rightGap ++ [fresh]) ++ flatten rightTail)).count tested % 2 := by
            intro marker member
            simpa only [flatten, List.append_assoc, List.singleton_append] using
              sameFirstPrefixes marker (List.mem_cons_of_mem fresh member)
          have tailBits := ih rightTail (leftPrefix ++ leftGap ++ [fresh])
            (rightPrefix ++ rightGap ++ [fresh]) leftGood.2.2 rightGood.2.2 markers.2
            extended tailTotal tailPrefixes
          change leftGap.count tested % 2 :: bits (gapProfile tested leftTail) =
            rightGap.count tested % 2 :: bits (gapProfile tested rightTail)
          rw [equalGap, tailBits]

theorem signature_gapBits (leftHead rightHead tested : Nat) (left right : Chain)
    (leftGood : WellFormed [leftHead] left) (rightGood : WellFormed [rightHead] right)
    (same : SameSignature ⟨leftHead,flatten left⟩ ⟨rightHead,flatten right⟩) :
    bits (gapProfile tested left) = bits (gapProfile tested right) := by
  have orders := signature_heads_introductions leftHead rightHead left right leftGood rightGood same
  apply gapBits_eq_of_prefixes left right [leftHead] [rightHead] tested leftGood rightGood orders.2
  · rw [orders.1]
  · exact ((Msg0446TailBudget.cap_eq_iff 2 _ _).1 (same.counts tested)).2
  · intro fresh member
    have leftMember : fresh ∈ (Word.mk leftHead (flatten left)).toList :=
      List.mem_cons_of_mem leftHead (introductions_mem_flatten left fresh member)
    have rightMember := (same.support fresh).mp leftMember
    exact same.prefixParity fresh leftMember rightMember tested

theorem map_bits_prependSectorCell (count : Nat) (cut : Bool) (blocks : List (List Nat)) :
    (prependSectorCell count cut blocks).map bits =
      prependSectorCell (count % 2) cut (blocks.map bits) := by
  cases blocks with
  | nil => rfl
  | cons block rest => cases cut <;> rfl

theorem sectorBits_eq_of_gapBits (leftWhole rightWhole : List Nat) (tested : Nat) (left right : Chain)
    (sameIntroductions : introductions left = introductions right)
    (sameCuts : ∀ fresh ∈ introductions left, leftWhole.count fresh = 1 ↔ rightWhole.count fresh = 1)
    (sameBits : bits (gapProfile tested left) = bits (gapProfile tested right)) :
    (sectorCounts leftWhole tested left).map bits = (sectorCounts rightWhole tested right).map bits := by
  induction left generalizing right with
  | stop leftGap =>
      cases right with
      | stop rightGap => exact congrArg (fun block => [block]) sameBits
      | step rightGap fresh tail => simp [introductions] at sameIntroductions
  | step leftGap fresh leftTail ih =>
      cases right with
      | stop rightGap => simp [introductions] at sameIntroductions
      | step rightGap nextFresh rightTail =>
          have markers := List.cons.inj sameIntroductions
          have equalFresh : fresh = nextFresh := markers.1
          subst nextFresh
          have cells := List.cons.inj sameBits
          have cellEqual : leftGap.count tested % 2 = rightGap.count tested % 2 := cells.1
          have cutEqual : decide (leftWhole.count fresh = 1) = decide (rightWhole.count fresh = 1) := by
            simp only [sameCuts fresh (by simp [introductions])]
          have tailBits := ih rightTail markers.2
            (fun marker member => sameCuts marker (List.mem_cons_of_mem fresh member)) cells.2
          rw [sectorCounts, sectorCounts, map_bits_prependSectorCell, map_bits_prependSectorCell,
            cellEqual, cutEqual, tailBits]

theorem signature_sectorBits (leftHead rightHead tested : Nat) (left right : Chain)
    (leftGood : WellFormed [leftHead] left) (rightGood : WellFormed [rightHead] right)
    (same : SameSignature ⟨leftHead,flatten left⟩ ⟨rightHead,flatten right⟩) :
    (sectorCounts (leftHead :: flatten left) tested left).map bits =
      (sectorCounts (rightHead :: flatten right) tested right).map bits := by
  apply sectorBits_eq_of_gapBits
  · exact (signature_heads_introductions leftHead rightHead left right leftGood rightGood same).2
  · intro fresh _
    exact same.simple fresh
  · exact signature_gapBits leftHead rightHead tested left right leftGood rightGood same

theorem signature_factor_sectorBits (left right : Word Nat) (same : SameSignature left right) (tested : Nat) :
    (sectorCounts left.toList tested (factor [left.head] left.tail)).map bits =
      (sectorCounts right.toList tested (factor [right.head] right.tail)).map bits := by
  have represented : SameSignature
      ⟨left.head,flatten (factor [left.head] left.tail)⟩
      ⟨right.head,flatten (factor [right.head] right.tail)⟩ := by
    simpa only [factor_flatten] using same
  simpa only [factor_flatten] using signature_sectorBits left.head right.head tested
    (factor [left.head] left.tail) (factor [right.head] right.tail)
    (factor_wellFormed [left.head] left.tail) (factor_wellFormed [right.head] right.tail) represented

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395GapParity

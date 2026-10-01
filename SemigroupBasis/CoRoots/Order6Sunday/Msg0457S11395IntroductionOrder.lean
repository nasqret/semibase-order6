import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ScalarBridge
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456RelativeFirstOrder

/-! Actual first-introduction chains recover the literal word first order.
The prefix before an introduction is the literal accumulated gap prefix,
even when the introduced letter is not globally simple. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395IntroductionOrder

open SemigroupBasis SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil
open Msg0457S11395SeenSwaps Msg0457S11395WordGaps Msg0457S11395Observations

theorem fresh_absent_before (prefixWords gap : List Nat) (fresh : Nat)
    (seen : AllSeen prefixWords gap) (absent : fresh ∉ prefixWords) :
    fresh ∉ prefixWords ++ gap := by
  intro member
  rcases List.mem_append.mp member with past | current
  · exact absent past
  · exact absent (seen fresh current)

theorem freshOrder_flatten (prefixWords : List Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) :
    freshOrder prefixWords (flatten chain) = introductions chain := by
  induction chain generalizing prefixWords with
  | stop gap => exact (freshOrder_empty_iff prefixWords gap).mpr good
  | step gap fresh tail ih =>
      have absent := fresh_absent_before prefixWords gap fresh good.1 good.2.1
      have gapEmpty := (freshOrder_empty_iff prefixWords gap).mpr good.1
      have sameSeen : freshOrder (fresh :: (prefixWords ++ gap)) (flatten tail) =
          freshOrder (prefixWords ++ gap ++ [fresh]) (flatten tail) := by
        apply freshOrder_seen_congr
        intro tested
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
        exact or_comm
      change freshOrder prefixWords (gap ++ fresh :: flatten tail) = fresh :: introductions tail
      rw [freshOrder_append, gapEmpty, List.nil_append, freshOrder_cons, if_neg absent,
        sameSeen, ih _ good.2.2]

theorem firstOrder_append (left right : List Nat) :
    firstOccurrenceSequence (left ++ right) =
      firstOccurrenceSequence left ++ freshOrder left right := by
  have emptySeen (letters : List Nat) : freshOrder [] letters = firstOccurrenceSequence letters := by
    unfold freshOrder
    apply List.filter_eq_self.mpr
    intro tested _
    simp
  have split := freshOrder_append [] left right
  rw [emptySeen (left ++ right), emptySeen left] at split
  simpa using split

theorem firstOrder_flatten (prefixWords : List Nat) (chain : Chain)
    (good : WellFormed prefixWords chain) :
    firstOccurrenceSequence (prefixWords ++ flatten chain) =
      firstOccurrenceSequence prefixWords ++ introductions chain := by
  rw [firstOrder_append, freshOrder_flatten prefixWords chain good]

theorem firstOrder_singleton (head : Nat) (chain : Chain) (good : WellFormed [head] chain) :
    firstOccurrenceSequence (head :: flatten chain) = head :: introductions chain := by
  simpa [firstOccurrenceSequence] using firstOrder_flatten [head] chain good

theorem signature_heads_introductions (leftHead rightHead : Nat) (left right : Chain)
    (leftGood : WellFormed [leftHead] left) (rightGood : WellFormed [rightHead] right)
    (same : SameSignature ⟨leftHead,flatten left⟩ ⟨rightHead,flatten right⟩) :
    leftHead = rightHead ∧ introductions left = introductions right := by
  have order := same.firstOrder
  change firstOccurrenceSequence (leftHead :: flatten left) =
    firstOccurrenceSequence (rightHead :: flatten right) at order
  rw [firstOrder_singleton leftHead left leftGood, firstOrder_singleton rightHead right rightGood] at order
  exact List.cons.inj order

theorem firstPrefix_step (prefixWords gap : List Nat) (fresh : Nat) (tail : Chain)
    (good : WellFormed prefixWords (.step gap fresh tail)) :
    S5_254.simplePrefixBefore fresh (prefixWords ++ flatten (.step gap fresh tail)) = prefixWords ++ gap := by
  change S5_254.simplePrefixBefore fresh (prefixWords ++ (gap ++ fresh :: flatten tail)) = _
  rw [← List.append_assoc]
  exact S5_254.simplePrefixBefore_split fresh (prefixWords ++ gap) (flatten tail)
    (fresh_absent_before prefixWords gap fresh good.1 good.2.1)

theorem introductions_mem_flatten (chain : Chain) (tested : Nat)
    (member : tested ∈ introductions chain) : tested ∈ flatten chain := by
  induction chain with
  | stop gap => simp [introductions] at member
  | step gap fresh tail ih =>
      rcases List.mem_cons.mp member with equal | later
      · exact List.mem_append_right gap (List.mem_cons.mpr (Or.inl equal))
      · exact List.mem_append_right gap (List.mem_cons_of_mem fresh (ih later))

theorem factor_firstOrder (word : Word Nat) :
    firstOccurrenceSequence word.toList = word.head :: introductions (factor [word.head] word.tail) := by
  simpa only [factor_flatten] using
    firstOrder_singleton word.head (factor [word.head] word.tail) (factor_wellFormed [word.head] word.tail)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395IntroductionOrder

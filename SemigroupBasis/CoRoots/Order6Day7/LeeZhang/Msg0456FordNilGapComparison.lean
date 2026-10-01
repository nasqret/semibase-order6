import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456FordNilBasis
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456RelativeFirstOrder

/-! Unrestricted exact-count comparison inside a gap of globally repeated
letters. Relative first order prevents moving two distinct first occurrences;
the actual guarded B23 swaps discharge every movement step. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis

private abbrev LD := S5_107.ListDerives basis

def AllRepeated (prefixWords gap suffix : List Nat) : Prop :=
  ∀ letter ∈ gap, 2 ≤ (prefixWords ++ gap ++ suffix).count letter

theorem freshOrder_append_seen (seen before after : List Nat)
    (old : ∀ letter ∈ before, letter ∈ seen) :
    freshOrder seen (before ++ after) = freshOrder seen after := by
  rw [freshOrder_append, (freshOrder_empty_iff seen before).2 old, List.nil_append]
  apply freshOrder_seen_congr
  intro tested
  constructor
  · intro member
    rcases List.mem_append.mp member with member | member
    · exact member
    · exact old tested member
  · intro member
    exact List.mem_append_left before member

theorem freshOrder_move_seen_head (seen before after : List Nat) (letter : Nat)
    (crossable : letter ∈ seen ∨ ∀ tested ∈ before, tested ∈ seen) :
    freshOrder seen (before ++ letter :: after) =
      freshOrder seen (letter :: (before ++ after)) := by
  rcases crossable with old | oldBefore
  · have oldExtended : letter ∈ seen ++ before := List.mem_append_left before old
    rw [freshOrder_append, freshOrder_cons (seen ++ before) letter after,
      if_pos oldExtended, freshOrder_cons seen letter (before ++ after), if_pos old,
      freshOrder_append]
  · rw [freshOrder_append_seen seen before (letter :: after) oldBefore,
      freshOrder_cons seen letter after, freshOrder_cons seen letter (before ++ after)]
    by_cases old : letter ∈ seen
    · rw [if_pos old, if_pos old]
      exact (freshOrder_append_seen seen before after oldBefore).symm
    · rw [if_neg old, if_neg old]
      apply congrArg (List.cons letter)
      exact (freshOrder_append_seen (letter :: seen) before after
        (fun tested member => List.mem_cons_of_mem letter (oldBefore tested member))).symm

private theorem splitFirst (letter : Nat) :
    ∀ {letters : List Nat}, letter ∈ letters →
      ∃ before after, letters = before ++ letter :: after ∧ letter ∉ before
  | [], member => by simp at member
  | head :: rest, member => by
      by_cases equal : head = letter
      · subst head
        exact ⟨[], rest, rfl, by simp⟩
      · have inRest : letter ∈ rest := by simpa [equal, Ne.symm equal] using member
        obtain ⟨before, after, shape, absent⟩ := splitFirst letter inRest
        refine ⟨head :: before, after, ?_, ?_⟩
        · simp [shape]
        · simp [Ne.symm equal, absent]

/-- Bubble one selected occurrence across a prefix that it is permitted
to cross. Every letter of the entire gap remains globally non-simple. -/
theorem moveGapHeadToFront (prefixWords before after suffix : List Nat) (letter : Nat)
    (crossable : letter ∈ prefixWords ∨ ∀ tested ∈ before, tested ∈ prefixWords)
    (repeated : AllRepeated prefixWords (before ++ letter :: after) suffix) :
    LD (prefixWords ++ before ++ letter :: after ++ suffix)
      (prefixWords ++ letter :: (before ++ after) ++ suffix) := by
  induction before generalizing prefixWords with
  | nil =>
      simpa using S5_107.ListDerives.refl (basis := basis)
        (prefixWords ++ letter :: after ++ suffix)
  | cons head rest induction =>
      have crossRest : letter ∈ prefixWords ++ [head] ∨
          ∀ tested ∈ rest, tested ∈ prefixWords ++ [head] := by
        rcases crossable with old | oldBefore
        · exact Or.inl (List.mem_append_left [head] old)
        · exact Or.inr (fun tested member => List.mem_append_left [head]
            (oldBefore tested (List.mem_cons_of_mem head member)))
      have repeatedRest : AllRepeated (prefixWords ++ [head]) (rest ++ letter :: after) suffix := by
        intro tested member
        have original := repeated tested (List.mem_cons_of_mem head member)
        simpa [List.append_assoc] using original
      have moved := induction (prefixWords ++ [head]) crossRest repeatedRest
      have headRepeated :
          2 ≤ (prefixWords ++ [head, letter] ++ (rest ++ after ++ suffix)).count head := by
        have original := repeated head (by simp)
        simp only [List.count_append, List.count_cons] at original ⊢
        omega
      have letterRepeated :
          2 ≤ (prefixWords ++ [head, letter] ++ (rest ++ after ++ suffix)).count letter := by
        have original := repeated letter (by simp)
        simp only [List.count_append, List.count_cons] at original ⊢
        omega
      have seen : head ∈ prefixWords ∨ letter ∈ prefixWords := by
        rcases crossable with old | oldBefore
        · exact Or.inr old
        · exact Or.inl (oldBefore head (by simp))
      have swapped := transportGuardedList
        (FordSwapCore.listDerivesSwapNonSimpleSeen prefixWords (rest ++ after ++ suffix)
          head letter headRepeated letterRepeated seen)
      have movedAligned :
          LD (prefixWords ++ (head :: rest) ++ letter :: after ++ suffix)
            (prefixWords ++ [head, letter] ++ (rest ++ after ++ suffix)) := by
        simpa [List.append_assoc] using moved
      simpa [List.append_assoc] using movedAligned.trans swapped

/-- Exact multiplicities and relative first-occurrence order suffice for
an arbitrary gap, provided no gap letter is globally simple. -/
theorem compareRepeatedGaps (prefixWords left right suffix : List Nat)
    (counts : ∀ tested, left.count tested = right.count tested)
    (order : freshOrder prefixWords left = freshOrder prefixWords right)
    (repeated : AllRepeated prefixWords left suffix) :
    LD (prefixWords ++ left ++ suffix) (prefixWords ++ right ++ suffix) := by
  induction right generalizing prefixWords left with
  | nil =>
      cases left with
      | nil => exact S5_107.ListDerives.refl _
      | cons head rest =>
          have impossible := counts head
          simp only [List.count_cons_self, List.count_nil] at impossible
          omega
  | cons letter tail induction =>
      have member : letter ∈ left := by
        apply List.count_pos_iff.mp
        rw [counts letter]
        simp
      obtain ⟨before, after, shape, first⟩ := splitFirst letter member
      have originalOrder : freshOrder prefixWords (before ++ letter :: after) =
          freshOrder prefixWords (letter :: tail) := by simpa [shape] using order
      have crossable : letter ∈ prefixWords ∨ ∀ tested ∈ before, tested ∈ prefixWords := by
        by_cases old : letter ∈ prefixWords
        · exact Or.inl old
        · exact Or.inr (first_head_barrier prefixWords before after tail letter old first originalOrder)
      have firstMove : LD (prefixWords ++ left ++ suffix)
          (prefixWords ++ letter :: (before ++ after) ++ suffix) := by
        simpa [shape, List.append_assoc] using
          moveGapHeadToFront prefixWords before after suffix letter crossable
            (by simpa [shape] using repeated)
      have tailCounts : ∀ tested, (before ++ after).count tested = tail.count tested := by
        intro tested
        have equal := counts tested
        rw [shape] at equal
        simp only [List.count_append, List.count_cons] at equal ⊢
        omega
      have matchedOrder : freshOrder prefixWords (letter :: (before ++ after)) =
          freshOrder prefixWords (letter :: tail) :=
        (freshOrder_move_seen_head prefixWords before after letter crossable).symm.trans originalOrder
      have tailOrderCons := freshOrder_cancel_head prefixWords (before ++ after) tail letter matchedOrder
      have adjust (letters : List Nat) :
          freshOrder (prefixWords ++ [letter]) letters = freshOrder (letter :: prefixWords) letters := by
        apply freshOrder_seen_congr
        intro tested
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        exact or_comm
      have tailOrder : freshOrder (prefixWords ++ [letter]) (before ++ after) =
          freshOrder (prefixWords ++ [letter]) tail :=
        (adjust (before ++ after)).trans (tailOrderCons.trans (adjust tail).symm)
      have tailRepeated : AllRepeated (prefixWords ++ [letter]) (before ++ after) suffix := by
        intro tested memberTail
        have memberLeft : tested ∈ left := by
          rw [shape]
          rcases List.mem_append.mp memberTail with memberBefore | memberAfter
          · exact List.mem_append_left _ memberBefore
          · exact List.mem_append_right _ (List.mem_cons_of_mem letter memberAfter)
        have equal : ((prefixWords ++ [letter]) ++ (before ++ after) ++ suffix).count tested =
            (prefixWords ++ left ++ suffix).count tested := by
          rw [shape]
          simp only [List.count_append, List.count_cons, List.count_nil]
          omega
        rw [equal]
        exact repeated tested memberLeft
      have remaining := induction (prefixWords ++ [letter]) (before ++ after) tailCounts tailOrder tailRepeated
      apply firstMove.trans
      simpa [List.append_assoc] using remaining

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

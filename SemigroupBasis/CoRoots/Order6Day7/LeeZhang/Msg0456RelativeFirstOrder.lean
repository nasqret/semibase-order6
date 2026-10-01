import SemigroupBasis.Examples.LeftRegularBandThree

/-! Pure first-occurrence bookkeeping for guarded gap comparison.
No semigroup-specific derivation or completeness premise is asserted. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis.Examples

def freshOrder (seen letters : List Nat) : List Nat :=
  (firstOccurrenceSequence letters).filter (fun letter => decide (letter ∉ seen))

theorem mem_freshOrder_iff (seen letters : List Nat) (letter : Nat) :
    letter ∈ freshOrder seen letters ↔ letter ∈ letters ∧ letter ∉ seen := by
  simp [freshOrder, mem_firstOccurrenceSequence_iff]

theorem freshOrder_seen_congr {left right : List Nat}
    (same : ∀ letter, letter ∈ left ↔ letter ∈ right) (letters : List Nat) :
    freshOrder left letters = freshOrder right letters := by
  unfold freshOrder
  apply List.filter_congr
  intro letter _
  simp only [same letter]

theorem freshOrder_cons (seen : List Nat) (letter : Nat) (rest : List Nat) :
    freshOrder seen (letter :: rest) =
      if letter ∈ seen then freshOrder seen rest
      else letter :: freshOrder (letter :: seen) rest := by
  by_cases old : letter ∈ seen
  · rw [if_pos old]
    simp only [freshOrder, firstOccurrenceSequence, List.filter_cons,
      show decide (letter ∉ seen) = false by simp [old], Bool.false_eq_true,
      if_false, List.filter_filter]
    apply List.filter_congr
    intro tested _
    by_cases equal : tested = letter
    · subst tested
      simp [old]
    · simp [equal]
  · rw [if_neg old]
    simp only [freshOrder, firstOccurrenceSequence, List.filter_cons,
      show decide (letter ∉ seen) = true by simp [old], if_true, List.filter_filter]
    apply congrArg (List.cons letter)
    apply List.filter_congr
    intro tested _
    simp [Bool.and_comm]

theorem freshOrder_add_seen {seen : List Nat} {letter : Nat}
    (old : letter ∈ seen) (letters : List Nat) :
    freshOrder (letter :: seen) letters = freshOrder seen letters := by
  apply freshOrder_seen_congr
  intro tested
  constructor
  · intro member
    rcases List.mem_cons.mp member with rfl | member
    · exact old
    · exact member
  · intro member
    exact List.mem_cons_of_mem _ member

theorem freshOrder_append (seen left right : List Nat) :
    freshOrder seen (left ++ right) =
      freshOrder seen left ++ freshOrder (seen ++ left) right := by
  induction left generalizing seen with
  | nil => simp [freshOrder, firstOccurrenceSequence]
  | cons letter rest induction =>
      rw [List.cons_append, freshOrder_cons, freshOrder_cons]
      by_cases old : letter ∈ seen
      · rw [if_pos old, if_pos old, induction]
        congr 1
        apply freshOrder_seen_congr
        intro tested
        simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (member | member)
          · exact Or.inl member
          · exact Or.inr (Or.inr member)
        · rintro (member | equal | member)
          · exact Or.inl member
          · subst tested
            exact Or.inl old
          · exact Or.inr member
      · rw [if_neg old, if_neg old, induction]
        simp only [List.cons_append]
        apply congrArg (List.cons letter)
        congr 1
        apply freshOrder_seen_congr
        intro tested
        simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (equal | member | member)
          · exact Or.inr (Or.inl equal)
          · exact Or.inl member
          · exact Or.inr (Or.inr member)
        · rintro (member | equal | member)
          · exact Or.inr (Or.inl member)
          · exact Or.inl equal
          · exact Or.inr (Or.inr member)

theorem freshOrder_empty_iff (seen letters : List Nat) :
    freshOrder seen letters = [] ↔ ∀ letter ∈ letters, letter ∈ seen := by
  constructor
  · intro empty letter member
    by_cases already : letter ∈ seen
    · exact already
    · have fresh := (mem_freshOrder_iff seen letters letter).2 ⟨member, already⟩
      simp [empty] at fresh
  · intro allSeen
    cases shape : freshOrder seen letters with
    | nil => rfl
    | cons letter rest =>
        have member : letter ∈ freshOrder seen letters := by simp [shape]
        have data := (mem_freshOrder_iff seen letters letter).1 member
        exact False.elim (data.2 (allSeen letter data.1))

/-- If the desired next letter is new, no different new first occurrence
may stand before it in a word with the same relative first order. -/
theorem first_head_barrier (seen before after target : List Nat) (letter : Nat)
    (newLetter : letter ∉ seen) (first : letter ∉ before)
    (order : freshOrder seen (before ++ letter :: after) =
      freshOrder seen (letter :: target)) :
    ∀ tested ∈ before, tested ∈ seen := by
  rw [freshOrder_append, freshOrder_cons seen letter target, if_neg newLetter] at order
  apply (freshOrder_empty_iff seen before).mp
  cases shape : freshOrder seen before with
  | nil => rfl
  | cons head tail =>
      rw [shape] at order
      have equal : head = letter := (List.cons.inj order).1
      have member : letter ∈ freshOrder seen before := by simp [shape, equal]
      exact False.elim (first ((mem_freshOrder_iff seen before letter).1 member).1)

theorem freshOrder_cancel_head (seen left right : List Nat) (letter : Nat)
    (order : freshOrder seen (letter :: left) = freshOrder seen (letter :: right)) :
    freshOrder (letter :: seen) left = freshOrder (letter :: seen) right := by
  rw [freshOrder_cons, freshOrder_cons] at order
  by_cases old : letter ∈ seen
  · rw [if_pos old, if_pos old] at order
    rw [freshOrder_add_seen old, freshOrder_add_seen old]
    exact order
  · rw [if_neg old, if_neg old] at order
    exact (List.cons.inj order).2

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484SimpleCrossing

/-! Arbitrary-list comparison using only proved global repeated-letter swaps.
Every movement retains the exact counts and the simple-separator data. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.SimplePrefix

open SemigroupBasis

theorem move_head_left {basis : List (Identity Nat)} (swaps : GlobalSwaps basis)
    (prefixWords gap after : List Nat) (letter : Nat)
    (allowed : ∀ tested ∈ gap,
      2 ≤ (prefixWords ++ gap ++ letter :: after).count letter ∧
      2 ≤ (prefixWords ++ gap ++ letter :: after).count tested) :
    S5_107.ListDerives basis (prefixWords ++ gap ++ letter :: after)
      (prefixWords ++ letter :: (gap ++ after)) ∧
    ExactSignature (prefixWords ++ gap ++ letter :: after)
      (prefixWords ++ letter :: (gap ++ after)) := by
  induction gap generalizing prefixWords with
  | nil =>
      simpa using And.intro (S5_107.ListDerives.refl (basis := basis) (prefixWords ++ letter :: after))
        (ExactSignature.refl (prefixWords ++ letter :: after))
  | cons head tail induction =>
      have restAllowed : ∀ tested ∈ tail,
          2 ≤ ((prefixWords ++ [head]) ++ tail ++ letter :: after).count letter ∧
          2 ≤ ((prefixWords ++ [head]) ++ tail ++ letter :: after).count tested := by
        intro tested member
        simpa [List.append_assoc] using allowed tested (List.mem_cons_of_mem head member)
      obtain ⟨move, preserve⟩ := induction (prefixWords ++ [head]) restAllowed
      have headAllowed := allowed head (by simp)
      have headHeavy : 2 ≤ (prefixWords ++ head :: letter :: (tail ++ after)).count head := by
        simp only [List.count_append, List.count_cons] at headAllowed ⊢
        omega
      have letterHeavy : 2 ≤ (prefixWords ++ head :: letter :: (tail ++ after)).count letter := by
        simp only [List.count_append, List.count_cons] at headAllowed ⊢
        omega
      have swap := swaps prefixWords head letter (tail ++ after) headHeavy letterHeavy
      have swapPreserves := swap_signature prefixWords head letter (tail ++ after) headHeavy letterHeavy
      have moveAligned : S5_107.ListDerives basis
          (prefixWords ++ (head :: tail) ++ letter :: after)
          (prefixWords ++ head :: letter :: (tail ++ after)) := by
        simpa [List.append_assoc] using move
      have preserveAligned : ExactSignature
          (prefixWords ++ (head :: tail) ++ letter :: after)
          (prefixWords ++ head :: letter :: (tail ++ after)) := by
        simpa [List.append_assoc] using preserve
      exact ⟨moveAligned.trans swap, preserveAligned.trans swapPreserves⟩

theorem compare_exact {basis : List (Identity Nat)} (swaps : GlobalSwaps basis)
    (prefixWords left right : List Nat)
    (same : ExactSignature (prefixWords ++ left) (prefixWords ++ right)) :
    S5_107.ListDerives basis (prefixWords ++ left) (prefixWords ++ right) := by
  induction right generalizing prefixWords left with
  | nil =>
      cases left with
      | nil => exact S5_107.ListDerives.refl _
      | cons head tail =>
          have impossible := same.counts head
          simp only [List.count_append, List.count_nil, List.count_cons_self] at impossible
          omega
  | cons letter tail induction =>
      have member : letter ∈ left := by
        apply List.count_pos_iff.mp
        have equality := same.counts letter
        simp only [List.count_append, List.count_cons_self] at equality
        omega
      obtain ⟨gap, after, shape, absent⟩ := PrefixCount.split_first letter member
      have aligned : ExactSignature (prefixWords ++ letter :: tail)
          (prefixWords ++ gap ++ letter :: after) := by
        simpa [shape, List.append_assoc] using same.symm
      have allowed := first_remaining_heavy prefixWords gap tail after letter absent aligned
      obtain ⟨move, preserve⟩ := move_head_left swaps prefixWords gap after letter allowed
      have firstMove : S5_107.ListDerives basis (prefixWords ++ left)
          (prefixWords ++ letter :: (gap ++ after)) := by
        simpa [shape, List.append_assoc] using move
      have tailSame : ExactSignature ((prefixWords ++ [letter]) ++ (gap ++ after))
          ((prefixWords ++ [letter]) ++ tail) := by
        have movedSame := preserve.symm.trans aligned.symm
        simpa [List.append_assoc] using movedSame
      have remaining := induction (prefixWords ++ [letter]) (gap ++ after) tailSame
      exact firstMove.trans (by simpa [List.append_assoc] using remaining)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.SimplePrefix

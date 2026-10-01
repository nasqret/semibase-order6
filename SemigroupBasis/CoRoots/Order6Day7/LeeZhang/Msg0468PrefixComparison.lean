import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468PrefixCount

/-! Arbitrary-word comparison from exact multiplicities and the capped
first-prefix counts. The explicit swap premise must be proved from a target
basis; this generic result does not supply that premise by stamping. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixCount

open SemigroupBasis

theorem sameBeforeTwo_swap (prefixWords : List Nat) (left right : Nat) (suffix : List Nat)
    (allowed : Crossable prefixWords left right) :
    SameBeforeTwo (prefixWords ++ left :: right :: suffix)
      (prefixWords ++ right :: left :: suffix) := by
  by_cases equal : left = right
  · subst right
    exact SameBeforeTwo.refl _
  intro tested separator
  by_cases old : separator ∈ prefixWords
  · rw [before_append_of_mem separator prefixWords _ old,
      before_append_of_mem separator prefixWords _ old]
  · rw [before_append_of_not_mem separator prefixWords _ old,
      before_append_of_not_mem separator prefixWords _ old]
    by_cases first : left = separator
    · subst separator
      have zero : prefixWords.count left = 0 := List.count_eq_zero_of_not_mem old
      have twice : 2 ≤ prefixWords.count right := by
        simp only [Crossable] at allowed
        omega
      by_cases selected : tested = right
      · subst tested
        simp only [before_self, before_cons_of_ne left right _ (Ne.symm equal),
          List.append_nil, List.count_append, List.count_cons_self, List.count_nil]
        omega
      · simp [before, Ne.symm equal, Ne.symm selected]
    · by_cases second : right = separator
      · subst separator
        have zero : prefixWords.count right = 0 := List.count_eq_zero_of_not_mem old
        have twice : 2 ≤ prefixWords.count left := by
          simp only [Crossable] at allowed
          omega
        by_cases selected : tested = left
        · subst tested
          simp only [before_self, before_cons_of_ne right left _ equal,
            List.append_nil, List.count_append, List.count_cons_self, List.count_nil]
          omega
        · simp [before, equal, Ne.symm selected]
      · simp only [before_cons_of_ne separator left _ first,
          before_cons_of_ne separator right _ second, List.count_append, List.count_cons]
        omega

def GuardedSwaps (basis : List (Identity Nat)) : Prop :=
  ∀ (prefixWords : List Nat) (left right : Nat) (suffix : List Nat),
    Crossable prefixWords left right →
      S5_107.ListDerives basis (prefixWords ++ left :: right :: suffix)
        (prefixWords ++ right :: left :: suffix)

theorem split_first (letter : Nat) :
    ∀ {letters : List Nat}, letter ∈ letters →
      ∃ gap after, letters = gap ++ letter :: after ∧ letter ∉ gap
  | [], member => by simp at member
  | head :: tail, member => by
      by_cases equal : head = letter
      · subst head
        exact ⟨[], tail, rfl, by simp⟩
      · have restMember : letter ∈ tail := by simpa [Ne.symm equal] using member
        obtain ⟨gap, after, shape, absent⟩ := split_first letter restMember
        exact ⟨head :: gap, after, by simp [shape], by simp [Ne.symm equal, absent]⟩

/-- Every adjacent movement has an actual basis derivation and preserves
the prefix signature. Empty gaps need no substitution or algebraic premise. -/
theorem move_head_left {basis : List (Identity Nat)} (swaps : GuardedSwaps basis)
    (prefixWords gap after : List Nat) (letter : Nat)
    (allowed : ∀ tested ∈ gap, Crossable prefixWords letter tested) :
    S5_107.ListDerives basis (prefixWords ++ gap ++ letter :: after)
      (prefixWords ++ letter :: (gap ++ after)) ∧
    SameBeforeTwo (prefixWords ++ gap ++ letter :: after)
      (prefixWords ++ letter :: (gap ++ after)) := by
  induction gap generalizing prefixWords with
  | nil =>
      simpa using And.intro (S5_107.ListDerives.refl (basis := basis) (prefixWords ++ letter :: after))
        (SameBeforeTwo.refl (prefixWords ++ letter :: after))
  | cons head tail induction =>
      have restAllowed : ∀ tested ∈ tail, Crossable (prefixWords ++ [head]) letter tested := by
        intro tested member
        exact (allowed tested (List.mem_cons_of_mem head member)).append [head]
      obtain ⟨move, preserve⟩ := induction (prefixWords ++ [head]) restAllowed
      have headAllowed := (allowed head (by simp)).symm
      have swap := swaps prefixWords head letter (tail ++ after) headAllowed
      have swapPreserves := sameBeforeTwo_swap prefixWords head letter (tail ++ after) headAllowed
      have moveAligned : S5_107.ListDerives basis
          (prefixWords ++ (head :: tail) ++ letter :: after)
          (prefixWords ++ head :: letter :: (tail ++ after)) := by
        simpa [List.append_assoc] using move
      have preserveAligned : SameBeforeTwo
          (prefixWords ++ (head :: tail) ++ letter :: after)
          (prefixWords ++ head :: letter :: (tail ++ after)) := by
        simpa [List.append_assoc] using preserve
      constructor
      · exact moveAligned.trans swap
      · exact preserveAligned.trans swapPreserves

/-- The unbounded comparison engine. Equal exact counts ensure a matching
occurrence exists; capped prefix counts justify every crossing. Induction is
on the whole target tail, with no alphabet-size or length restriction. -/
theorem compare_exact_counts {basis : List (Identity Nat)} (swaps : GuardedSwaps basis)
    (prefixWords left right : List Nat)
    (counts : ∀ tested, left.count tested = right.count tested)
    (same : SameBeforeTwo (prefixWords ++ left) (prefixWords ++ right)) :
    S5_107.ListDerives basis (prefixWords ++ left) (prefixWords ++ right) := by
  induction right generalizing prefixWords left with
  | nil =>
      cases left with
      | nil => exact S5_107.ListDerives.refl _
      | cons head tail =>
          have impossible := counts head
          simp only [List.count_nil, List.count_cons_self] at impossible
          omega
  | cons letter tail induction =>
      have member : letter ∈ left := by
        apply List.count_pos_iff.mp
        rw [counts letter]
        simp
      obtain ⟨gap, after, shape, absent⟩ := split_first letter member
      have aligned : SameBeforeTwo (prefixWords ++ letter :: tail)
          (prefixWords ++ gap ++ letter :: after) := by
        simpa [shape, List.append_assoc] using same.symm
      have allowed := first_remaining_crossable prefixWords gap tail after letter absent aligned
      obtain ⟨move, preserve⟩ := move_head_left swaps prefixWords gap after letter allowed
      have firstMove : S5_107.ListDerives basis (prefixWords ++ left)
          (prefixWords ++ letter :: (gap ++ after)) := by
        simpa [shape, List.append_assoc] using move
      have tailCounts : ∀ tested, (gap ++ after).count tested = tail.count tested := by
        intro tested
        have equality := counts tested
        rw [shape] at equality
        simp only [List.count_append, List.count_cons] at equality ⊢
        omega
      have tailSame : SameBeforeTwo ((prefixWords ++ [letter]) ++ (gap ++ after))
          ((prefixWords ++ [letter]) ++ tail) := by
        have movedSame := preserve.symm.trans aligned.symm
        simpa [List.append_assoc] using movedSame
      have remaining := induction (prefixWords ++ [letter]) (gap ++ after) tailCounts tailSame
      exact firstMove.trans (by simpa [List.append_assoc] using remaining)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixCount

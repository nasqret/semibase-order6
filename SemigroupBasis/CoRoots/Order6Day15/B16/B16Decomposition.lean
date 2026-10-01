import SemigroupBasis.CoRoots.Order6Day15.B16.B16SegmentChain

namespace SemigroupBasis.CoRoots.Order6Day15.B16.Reach

/-- Stop immediately before the first letter in the fixed global nonsimple support. -/
def splitFront (ns : List Nat) : List Nat → List Nat × List Nat
  | [] => ([],[])
  | a :: xs => if a ∈ ns then ([],a :: xs) else
      let cut := splitFront ns xs
      (a :: cut.1,cut.2)

theorem splitFront_join (ns xs : List Nat) :
    (splitFront ns xs).1 ++ (splitFront ns xs).2 = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases ha : a ∈ ns
      · rw [splitFront, if_pos ha]; rfl
      · rw [splitFront, if_neg ha]
        exact congrArg (List.cons a) ih

theorem splitFront_avoid (ns xs : List Nat) :
    ∀ a ∈ (splitFront ns xs).1, a ∉ ns := by
  induction xs with
  | nil => exact fun _ h => False.elim (List.not_mem_nil h)
  | cons a xs ih =>
      by_cases ha : a ∈ ns
      · rw [splitFront, if_pos ha]
        exact fun _ h => False.elim (List.not_mem_nil h)
      · rw [splitFront, if_neg ha]
        intro b hb
        rcases List.mem_cons.mp hb with eq | mem
        · subst b; exact ha
        · exact ih b mem

theorem splitFront_head (ns xs : List Nat) (a : Nat) (tail : List Nat)
    (eq : (splitFront ns xs).2 = a :: tail) : a ∈ ns := by
  induction xs with
  | nil => cases eq
  | cons b xs ih =>
      by_cases hb : b ∈ ns
      · rw [splitFront, if_pos hb] at eq
        have heads : b = a := List.cons.inj eq |>.1
        exact heads ▸ hb
      · rw [splitFront, if_neg hb] at eq
        exact ih eq

/-- Initial ns-run, followed by every non-ns separator and its following ns-run. -/
def splitGaps (ns : List Nat) : List Nat → List Nat × List (Nat × List Nat)
  | [] => ([],[])
  | a :: xs =>
      let cut := splitGaps ns xs
      if a ∈ ns then (a :: cut.1,cut.2) else ([],(a,cut.1) :: cut.2)

theorem splitGaps_join (ns xs : List Nat) :
    (splitGaps ns xs).1 ++ flattenSegments (splitGaps ns xs).2 = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases ha : a ∈ ns
      · rw [splitGaps, if_pos ha]
        exact congrArg (List.cons a) ih
      · rw [splitGaps, if_neg ha]
        exact congrArg (List.cons a) ih

theorem splitGaps_first_covered (ns xs : List Nat) :
    ∀ a ∈ (splitGaps ns xs).1, a ∈ ns := by
  induction xs with
  | nil => exact fun _ h => False.elim (List.not_mem_nil h)
  | cons a xs ih =>
      by_cases ha : a ∈ ns
      · rw [splitGaps, if_pos ha]
        intro b hb
        rcases List.mem_cons.mp hb with eq | mem
        · subst b; exact ha
        · exact ih b mem
      · rw [splitGaps, if_neg ha]
        exact fun _ h => False.elim (List.not_mem_nil h)

theorem splitGaps_later_covered (ns xs : List Nat) :
    ∀ seg ∈ (splitGaps ns xs).2, ∀ a ∈ seg.2, a ∈ ns := by
  induction xs with
  | nil => exact fun _ h => False.elim (List.not_mem_nil h)
  | cons a xs ih =>
      by_cases ha : a ∈ ns
      · rw [splitGaps, if_pos ha]
        exact ih
      · rw [splitGaps, if_neg ha]
        intro seg hs
        rcases List.mem_cons.mp hs with eq | mem
        · subst seg
          exact splitGaps_first_covered ns xs
        · exact ih seg mem

theorem splitGaps_separators (ns xs : List Nat) :
    ∀ seg ∈ (splitGaps ns xs).2, seg.1 ∉ ns := by
  induction xs with
  | nil => exact fun _ h => False.elim (List.not_mem_nil h)
  | cons a xs ih =>
      by_cases ha : a ∈ ns
      · rw [splitGaps, if_pos ha]
        exact ih
      · rw [splitGaps, if_neg ha]
        intro seg hs
        rcases List.mem_cons.mp hs with eq | mem
        · subst seg; exact ha
        · exact ih seg mem

end SemigroupBasis.CoRoots.Order6Day15.B16.Reach

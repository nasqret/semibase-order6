import SemigroupBasis.CoRoots.S5_107ListDerives

/-! Table-independent combinatorics for index-three power absorption.
No semigroup, basis, bounded word window, or completeness field is assumed.
The two internal gaps may independently be empty. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2

theorem exists_two_occurrence_split (letter : Nat) :
    ∀ {letters : List Nat}, 2 ≤ letters.count letter →
      ∃ before middle after,
        letters = before ++ letter :: middle ++ letter :: after
  | [], count => by simp at count
  | first :: rest, count => by
      by_cases equal : first = letter
      · subst first
        have positive : 0 < rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨middle, after, shape⟩ := List.mem_iff_append.mp (List.count_pos_iff.mp positive)
        exact ⟨[], middle, after, by simp [shape]⟩
      · have restCount : 2 ≤ rest.count letter := by simpa [equal] using count
        obtain ⟨before, middle, after, shape⟩ := exists_two_occurrence_split letter restCount
        exact ⟨first :: before, middle, after, by simp [shape]⟩

theorem exists_three_occurrence_split (letter : Nat) :
    ∀ {letters : List Nat}, 3 ≤ letters.count letter →
      ∃ before firstGap secondGap after,
        letters = before ++ [letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter] ++ after
  | [], count => by simp at count
  | first :: rest, count => by
      by_cases equal : first = letter
      · subst first
        have repeated : 2 ≤ rest.count letter := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨firstGap, secondGap, after, shape⟩ := exists_two_occurrence_split letter repeated
        exact ⟨[], firstGap, secondGap, after, by simp [shape, List.append_assoc]⟩
      · have restCount : 3 ≤ rest.count letter := by simpa [equal] using count
        obtain ⟨before, firstGap, secondGap, after, shape⟩ := exists_three_occurrence_split letter restCount
        exact ⟨first :: before, firstGap, secondGap, after, by simp [shape, List.append_assoc]⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2

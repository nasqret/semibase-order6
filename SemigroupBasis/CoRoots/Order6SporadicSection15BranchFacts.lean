import SemigroupBasis.CoRoots.Order6SporadicSection15CanonicalData

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace CanonicalData

/-! ## Inverse facts for the canonical branch classifier -/

theorem sortedHighCountLetters_eq_nil_of_branch_alpha
    {letters : List Nat}
    (branch : canonicalBranch letters = .alpha) :
    sortedHighCountLetters letters = [] := by
  cases high : sortedHighCountLetters letters with
  | nil => rfl
  | cons first rest =>
      simp [canonicalBranch, high] at branch

theorem sortedDoubledLetters_ne_nil_of_branch_alpha
    {letters : List Nat}
    (branch : canonicalBranch letters = .alpha) :
    sortedDoubledLetters letters ≠ [] := by
  intro doubled
  have high :=
    sortedHighCountLetters_eq_nil_of_branch_alpha branch
  simp [canonicalBranch, high, doubled] at branch

theorem sortedHighCountLetters_ne_nil_of_branch_beta
    {letters : List Nat}
    (branch : canonicalBranch letters = .beta) :
    sortedHighCountLetters letters ≠ [] := by
  intro high
  cases doubled : sortedDoubledLetters letters with
  | nil =>
      simp [canonicalBranch, high, doubled] at branch
  | cons first rest =>
      simp [canonicalBranch, high, doubled] at branch

theorem sortedHighCountLetters_eq_nil_of_branch_simple
    {letters : List Nat}
    (branch : canonicalBranch letters = .simple) :
    sortedHighCountLetters letters = [] := by
  cases high : sortedHighCountLetters letters with
  | nil => rfl
  | cons first rest =>
      simp [canonicalBranch, high] at branch

theorem sortedDoubledLetters_eq_nil_of_branch_simple
    {letters : List Nat}
    (branch : canonicalBranch letters = .simple) :
    sortedDoubledLetters letters = [] := by
  have high :=
    sortedHighCountLetters_eq_nil_of_branch_simple branch
  cases doubled : sortedDoubledLetters letters with
  | nil => rfl
  | cons first rest =>
      simp [canonicalBranch, high, doubled] at branch

theorem canonicalBranch_eq_simple_iff (letters : List Nat) :
    canonicalBranch letters = .simple ↔
      sortedHighCountLetters letters = [] ∧
        sortedDoubledLetters letters = [] := by
  constructor
  · intro branch
    exact
      ⟨sortedHighCountLetters_eq_nil_of_branch_simple branch,
        sortedDoubledLetters_eq_nil_of_branch_simple branch⟩
  · rintro ⟨high, doubled⟩
    exact canonicalBranch_eq_simple letters high doubled

theorem canonicalBranch_eq_alpha_iff (letters : List Nat) :
    canonicalBranch letters = .alpha ↔
      sortedHighCountLetters letters = [] ∧
        sortedDoubledLetters letters ≠ [] := by
  constructor
  · intro branch
    exact
      ⟨sortedHighCountLetters_eq_nil_of_branch_alpha branch,
        sortedDoubledLetters_ne_nil_of_branch_alpha branch⟩
  · rintro ⟨high, doubledNonempty⟩
    obtain ⟨first, rest, doubled⟩ :=
      List.exists_cons_of_ne_nil doubledNonempty
    exact canonicalBranch_eq_alpha letters high doubled

theorem canonicalBranch_eq_beta_iff (letters : List Nat) :
    canonicalBranch letters = .beta ↔
      sortedHighCountLetters letters ≠ [] := by
  constructor
  · exact sortedHighCountLetters_ne_nil_of_branch_beta
  · intro highNonempty
    obtain ⟨first, rest, high⟩ :=
      List.exists_cons_of_ne_nil highNonempty
    exact canonicalBranch_eq_beta letters high

/-! ## Immediate multiplicity consequences -/

theorem exists_count_eq_two_of_branch_alpha
    {letters : List Nat}
    (branch : canonicalBranch letters = .alpha) :
    ∃ letter, letters.count letter = 2 := by
  have doubledNonempty :=
    sortedDoubledLetters_ne_nil_of_branch_alpha branch
  obtain ⟨letter, rest, doubled⟩ :=
    List.exists_cons_of_ne_nil doubledNonempty
  refine ⟨letter, (sortedDoubledLetters_mem_iff letter letters).1 ?_⟩
  rw [doubled]
  simp

theorem count_le_two_of_branch_alpha
    {letters : List Nat}
    (branch : canonicalBranch letters = .alpha)
    (letter : Nat) :
    letters.count letter ≤ 2 := by
  have high :=
    sortedHighCountLetters_eq_nil_of_branch_alpha branch
  apply Decidable.byContradiction
  intro notLe
  have countHigh : 3 ≤ letters.count letter := by omega
  have member :=
    (sortedHighCountLetters_mem_iff letter letters).2 countHigh
  rw [high] at member
  simp at member

theorem exists_count_ge_three_of_branch_beta
    {letters : List Nat}
    (branch : canonicalBranch letters = .beta) :
    ∃ letter, 3 ≤ letters.count letter := by
  have highNonempty :=
    sortedHighCountLetters_ne_nil_of_branch_beta branch
  obtain ⟨letter, rest, high⟩ :=
    List.exists_cons_of_ne_nil highNonempty
  refine ⟨letter, (sortedHighCountLetters_mem_iff letter letters).1 ?_⟩
  rw [high]
  simp

theorem count_le_one_of_branch_simple
    {letters : List Nat}
    (branch : canonicalBranch letters = .simple)
    (letter : Nat) :
    letters.count letter ≤ 1 := by
  have high :=
    sortedHighCountLetters_eq_nil_of_branch_simple branch
  have doubled :=
    sortedDoubledLetters_eq_nil_of_branch_simple branch
  apply Decidable.byContradiction
  intro notLe
  have countMultiple : 2 ≤ letters.count letter := by omega
  have member :=
    (sortedMultiplicityClasses_mem_iff letter letters).2 countMultiple
  rw [doubled, high] at member
  simp at member

end CanonicalData

end SemigroupBasis.CoRoots.Order6SporadicSection15

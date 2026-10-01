import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedMaximalFactors

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries

open MaximalFactors

theorem good_tail (classify : Nat → Bool) (first : Word Nat)
    (rest : List (Word Nat)) (good : Good classify (first :: rest)) :
    Good classify rest := by
  cases good with
  | last uniform => exact Good.nil
  | step uniform different tailGood => exact tailGood

theorem good_after_prefix (classify : Nat → Bool) (before after : List (Word Nat))
    (good : Good classify (before ++ after)) : Good classify after := by
  induction before with
  | nil => exact good
  | cons first rest ih =>
      have tailGood : Good classify (rest ++ after) :=
        good_tail classify first (rest ++ after) good
      exact ih tailGood

theorem flatten_append (before after : List (Word Nat)) :
    flatten (before ++ after) = flatten before ++ flatten after := by
  induction before with
  | nil => rfl
  | cons first rest ih =>
      change first.toList ++ flatten (rest ++ after) =
        (first.toList ++ flatten rest) ++ flatten after
      rw [ih, List.append_assoc]

theorem split_member (piece : Word Nat) (pieces : List (Word Nat))
    (member : piece ∈ pieces) :
    ∃ before after : List (Word Nat), pieces = before ++ piece :: after := by
  induction pieces with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | later
      · cases equal
        exact ⟨[], rest, rfl⟩
      · obtain ⟨before, after, split⟩ := ih later
        refine ⟨first :: before, after, ?_⟩
        change first :: rest = first :: (before ++ piece :: after)
        rw [split]

theorem word_head_member (piece : Word Nat) : piece.head ∈ piece.toList :=
  List.mem_cons.mpr (Or.inl rfl)

theorem good_boundary_letters (classify : Nat → Bool) (first second : Word Nat)
    (rest : List (Word Nat)) (good : Good classify (first :: second :: rest))
    (left right : Nat) (leftMember : left ∈ first.toList)
    (rightMember : right ∈ second.toList) : classify left ≠ classify right := by
  have firstMember : first ∈ first :: second :: rest := List.mem_cons.mpr (Or.inl rfl)
  have secondMember : second ∈ first :: second :: rest :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have leftClass : classify left = classify first.head :=
    good_member_constant classify good firstMember left leftMember
  have rightClass : classify right = classify second.head :=
    good_member_constant classify good secondMember right rightMember
  have different : classify first.head ≠ classify second.head :=
    good_first_boundary classify first second rest good
  intro equal
  have impossible : classify first.head = classify second.head :=
    leftClass.symm.trans (equal.trans rightClass)
  exact different impossible

/-- Every selected run is a contiguous factor, with all adjacent run letters
in the other classification. The exact ordered word is retained. -/
theorem factor_witness (classify : Nat → Bool) (letters : List Nat)
    (piece : Word Nat) (member : piece ∈ decompose classify letters) :
    ∃ before after : List (Word Nat),
      decompose classify letters = before ++ piece :: after ∧
      letters = flatten before ++ (piece.toList ++ flatten after) ∧
      Constant classify piece ∧
      (∀ earlier last, before = earlier ++ [last] →
        ∀ value ∈ last.toList, classify value ≠ classify piece.head) ∧
      (∀ next later, after = next :: later →
        ∀ value ∈ next.toList, classify value ≠ classify piece.head) := by
  obtain ⟨before, after, split⟩ := split_member piece (decompose classify letters) member
  have allGood : Good classify (before ++ piece :: after) := by
    rw [← split]
    exact decompose_good classify letters
  have rendered : letters = flatten before ++ (piece.toList ++ flatten after) := by
    calc
      letters = flatten (decompose classify letters) := (flatten_decompose classify letters).symm
      _ = flatten (before ++ piece :: after) := congrArg flatten split
      _ = flatten before ++ flatten (piece :: after) := flatten_append before (piece :: after)
      _ = flatten before ++ (piece.toList ++ flatten after) := rfl
  have uniform : Constant classify piece :=
    good_member_constant classify (decompose_good classify letters) member
  refine ⟨before, after, split, rendered, uniform, ?_, ?_⟩
  · intro earlier last boundary value inside
    have adjacent : Good classify (last :: piece :: after) := by
      have expanded : Good classify ((earlier ++ [last]) ++ piece :: after) := by
        rw [← boundary]
        exact allGood
      rw [List.append_assoc] at expanded
      exact good_after_prefix classify earlier (last :: piece :: after) expanded
    exact good_boundary_letters classify last piece after adjacent value piece.head
      inside (word_head_member piece)
  · intro next later boundary value inside
    have adjacent : Good classify (piece :: next :: later) := by
      have remaining := good_after_prefix classify before (piece :: after) allGood
      rw [boundary] at remaining
      exact remaining
    have apart : classify piece.head ≠ classify value :=
      good_boundary_letters classify piece next later adjacent piece.head value
        (word_head_member piece) inside
    exact fun equal => apart equal.symm

theorem false_of_ne_true (tag : Bool) (different : tag ≠ true) : tag = false := by
  cases tag with
  | false => rfl
  | true => exact False.elim (different rfl)

/-- A binary run has explicit complementary neighbours on both sides. These
are actual word-factor witnesses, not a C1/C2 relation or reach assumption. -/
theorem maximal_binary_factor_witness (x y : Nat) (letters : List Nat)
    (piece : Word Nat) (member : piece ∈ decompose (binaryTag x y) letters)
    (binary : binaryTag x y piece.head = true) :
    ∃ before after : List (Word Nat),
      decompose (binaryTag x y) letters = before ++ piece :: after ∧
      letters = flatten before ++ (piece.toList ++ flatten after) ∧
      (∀ value ∈ piece.toList, value = x ∨ value = y) ∧
      (∀ earlier last, before = earlier ++ [last] →
        ∀ value ∈ last.toList, value ≠ x ∧ value ≠ y) ∧
      (∀ next later, after = next :: later →
        ∀ value ∈ next.toList, value ≠ x ∧ value ≠ y) := by
  obtain ⟨before, after, split, rendered, uniform, leftOutside, rightOutside⟩ :=
    factor_witness (binaryTag x y) letters piece member
  refine ⟨before, after, split, rendered, ?_, ?_, ?_⟩
  · intro value inside
    exact (binaryTag_true x y value).mp ((uniform value inside).trans binary)
  · intro earlier last boundary value inside
    have different : binaryTag x y value ≠ true := by
      rw [← binary]
      exact leftOutside earlier last boundary value inside
    exact binaryTag_false x y value (false_of_ne_true (binaryTag x y value) different)
  · intro next later boundary value inside
    have different : binaryTag x y value ≠ true := by
      rw [← binary]
      exact rightOutside next later boundary value inside
    exact binaryTag_false x y value (false_of_ne_true (binaryTag x y value) different)

theorem word_maximal_binary_factor_witness (x y : Nat) (word piece : Word Nat)
    (member : piece ∈ decompose (binaryTag x y) word.toList)
    (binary : binaryTag x y piece.head = true) :
    ∃ before after : List (Word Nat),
      word.toList = flatten before ++ (piece.toList ++ flatten after) ∧
      (∀ value ∈ piece.toList, value = x ∨ value = y) ∧
      (∀ earlier last, before = earlier ++ [last] →
        ∀ value ∈ last.toList, value ≠ x ∧ value ≠ y) ∧
      (∀ next later, after = next :: later →
        ∀ value ∈ next.toList, value ≠ x ∧ value ≠ y) := by
  obtain ⟨before, after, split, rendered, uniform, leftOutside, rightOutside⟩ :=
    maximal_binary_factor_witness x y word.toList piece member binary
  exact ⟨before, after, rendered, uniform, leftOutside, rightOutside⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.good_tail
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.good_after_prefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.flatten_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.split_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.word_head_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.good_boundary_letters
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.factor_witness
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.false_of_ne_true
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.maximal_binary_factor_witness
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorBoundaries.word_maximal_binary_factor_witness

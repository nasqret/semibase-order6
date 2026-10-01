import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedPerfectSweeps

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors

/-- A run has one classification, including its first letter. -/
def Constant (classify : Nat → Bool) (piece : Word Nat) : Prop :=
  ∀ letter ∈ piece.toList, classify letter = classify piece.head

/-- Nonempty homogeneous runs with a classification change at every boundary. -/
inductive Good (classify : Nat → Bool) : List (Word Nat) → Prop
  | nil : Good classify []
  | last {piece : Word Nat} : Constant classify piece → Good classify [piece]
  | step {first second : Word Nat} {rest : List (Word Nat)} :
      Constant classify first → classify first.head ≠ classify second.head →
      Good classify (second :: rest) → Good classify (first :: second :: rest)

def insertLetter (classify : Nat → Bool) (letter : Nat) :
    List (Word Nat) → List (Word Nat)
  | [] => [Word.singleton letter]
  | piece :: rest =>
      if classify letter = classify piece.head then
        ⟨letter, piece.toList⟩ :: rest
      else Word.singleton letter :: piece :: rest

def decompose (classify : Nat → Bool) : List Nat → List (Word Nat)
  | [] => []
  | letter :: rest => insertLetter classify letter (decompose classify rest)

def flatten : List (Word Nat) → List Nat
  | [] => []
  | piece :: rest => piece.toList ++ flatten rest

theorem flatten_insert (classify : Nat → Bool) (letter : Nat)
    (pieces : List (Word Nat)) :
    flatten (insertLetter classify letter pieces) = letter :: flatten pieces := by
  cases pieces with
  | nil => rfl
  | cons piece rest =>
      by_cases same : classify letter = classify piece.head
      · simp only [insertLetter, if_pos same]
        rfl
      · simp only [insertLetter, if_neg same]
        rfl

theorem flatten_decompose (classify : Nat → Bool) (letters : List Nat) :
    flatten (decompose classify letters) = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      change flatten (insertLetter classify letter (decompose classify rest)) = letter :: rest
      rw [flatten_insert, ih]

theorem constant_singleton (classify : Nat → Bool) (letter : Nat) :
    Constant classify (Word.singleton letter) := by
  intro value member
  have equal : value = letter := by
    simpa only [Word.singleton, Word.toList, List.mem_singleton] using member
  exact congrArg classify equal

theorem constant_prepend (classify : Nat → Bool) (letter : Nat) (piece : Word Nat)
    (uniform : Constant classify piece) (same : classify letter = classify piece.head) :
    Constant classify ⟨letter, piece.toList⟩ := by
  intro value member
  change value ∈ letter :: piece.toList at member
  rcases List.mem_cons.mp member with equal | inside
  · exact congrArg classify equal
  · exact (uniform value inside).trans same.symm

theorem insert_good (classify : Nat → Bool) (letter : Nat)
    {pieces : List (Word Nat)} (good : Good classify pieces) :
    Good classify (insertLetter classify letter pieces) := by
  cases good with
  | nil => exact Good.last (constant_singleton classify letter)
  | @last piece uniform =>
      by_cases same : classify letter = classify piece.head
      · rw [insertLetter, if_pos same]
        exact Good.last (constant_prepend classify letter piece uniform same)
      · rw [insertLetter, if_neg same]
        exact Good.step (constant_singleton classify letter) same (Good.last uniform)
  | @step first second rest uniform different tailGood =>
      by_cases same : classify letter = classify first.head
      · rw [insertLetter, if_pos same]
        have boundary : classify letter ≠ classify second.head := by
          intro equal
          exact different (same.symm.trans equal)
        exact Good.step (constant_prepend classify letter first uniform same) boundary tailGood
      · rw [insertLetter, if_neg same]
        exact Good.step (constant_singleton classify letter) same
          (Good.step uniform different tailGood)

theorem decompose_good (classify : Nat → Bool) (letters : List Nat) :
    Good classify (decompose classify letters) := by
  induction letters with
  | nil => exact Good.nil
  | cons letter rest ih => exact insert_good classify letter ih

theorem good_member_constant (classify : Nat → Bool) {pieces : List (Word Nat)}
    (good : Good classify pieces) {piece : Word Nat} (member : piece ∈ pieces) :
    Constant classify piece := by
  induction good generalizing piece with
  | nil => cases member
  | last uniform =>
      have equal := List.mem_singleton.mp member
      cases equal
      exact uniform
  | step uniform different tailGood ih =>
      rcases List.mem_cons.mp member with equal | inside
      · cases equal
        exact uniform
      · exact ih inside

theorem good_first_boundary (classify : Nat → Bool) (first second : Word Nat)
    (rest : List (Word Nat)) (good : Good classify (first :: second :: rest)) :
    classify first.head ≠ classify second.head := by
  cases good with
  | step uniform different tailGood => exact different

theorem piece_nonempty (piece : Word Nat) : piece.toList ≠ [] := by
  intro empty
  cases empty

theorem mem_flatten (letter : Nat) (pieces : List (Word Nat)) :
    letter ∈ flatten pieces ↔ ∃ piece, piece ∈ pieces ∧ letter ∈ piece.toList := by
  induction pieces with
  | nil =>
      constructor
      · intro member
        cases member
      · rintro ⟨piece, member, inside⟩
        cases member
  | cons piece rest ih =>
      change letter ∈ piece.toList ++ flatten rest ↔ _
      constructor
      · intro member
        rcases List.mem_append.mp member with inside | later
        · exact ⟨piece, List.mem_cons.mpr (Or.inl rfl), inside⟩
        · obtain ⟨other, member, inside⟩ := ih.mp later
          exact ⟨other, List.mem_cons.mpr (Or.inr member), inside⟩
      · rintro ⟨other, member, inside⟩
        rcases List.mem_cons.mp member with equal | later
        · cases equal
          exact List.mem_append.mpr (Or.inl inside)
        · exact List.mem_append.mpr (Or.inr (ih.mpr ⟨other, later, inside⟩))

theorem decompose_covers (classify : Nat → Bool) (letter : Nat) (letters : List Nat) :
    letter ∈ letters ↔
      ∃ piece, piece ∈ decompose classify letters ∧ letter ∈ piece.toList := by
  have covered := mem_flatten letter (decompose classify letters)
  simpa only [flatten_decompose] using covered

def binaryTag (x y letter : Nat) : Bool := decide (letter = x ∨ letter = y)

theorem binaryTag_true (x y letter : Nat) :
    binaryTag x y letter = true ↔ letter = x ∨ letter = y := by
  constructor
  · intro tag
    exact of_decide_eq_true tag
  · intro member
    exact decide_eq_true member

theorem binaryTag_false (x y letter : Nat) (tag : binaryTag x y letter = false) :
    letter ≠ x ∧ letter ≠ y := by
  constructor
  · intro equal
    have positive : binaryTag x y letter = true := (binaryTag_true x y letter).mpr (Or.inl equal)
    have impossible : (false : Bool) = true := tag.symm.trans positive
    cases impossible
  · intro equal
    have positive : binaryTag x y letter = true := (binaryTag_true x y letter).mpr (Or.inr equal)
    have impossible : (false : Bool) = true := tag.symm.trans positive
    cases impossible

/-- Total, order-preserving maximal binary runs and their complementary separators.
This does not assume a C1/C2 witness, a derivation, or the completeness theorem. -/
theorem maximal_binary_cover (x y : Nat) (letters : List Nat) :
    ∃ pieces : List (Word Nat),
      flatten pieces = letters ∧ Good (binaryTag x y) pieces ∧
      (∀ piece ∈ pieces, piece.toList ≠ []) ∧
      (∀ piece ∈ pieces,
        (∀ letter ∈ piece.toList, letter = x ∨ letter = y) ∨
        (∀ letter ∈ piece.toList, letter ≠ x ∧ letter ≠ y)) := by
  let pieces := decompose (binaryTag x y) letters
  have good : Good (binaryTag x y) pieces := decompose_good (binaryTag x y) letters
  refine ⟨pieces, flatten_decompose (binaryTag x y) letters, good, ?_, ?_⟩
  · intro piece member
    exact piece_nonempty piece
  · intro piece member
    have uniform : Constant (binaryTag x y) piece := good_member_constant (binaryTag x y) good member
    cases tag : binaryTag x y piece.head with
    | false =>
        right
        intro letter inside
        exact binaryTag_false x y letter ((uniform letter inside).trans tag)
    | true =>
        left
        intro letter inside
        exact (binaryTag_true x y letter).mp ((uniform letter inside).trans tag)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.flatten_insert
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.flatten_decompose
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.constant_singleton
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.constant_prepend
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.insert_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.decompose_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.good_member_constant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.good_first_boundary
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.piece_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.mem_flatten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.decompose_covers
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.binaryTag_true
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.binaryTag_false
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalFactors.maximal_binary_cover

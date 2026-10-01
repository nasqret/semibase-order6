import SemigroupBasis.CoRoots.Order6SporadicSection12

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis

/-!
This file contains the finite-support form of the connected-basis reduction
used in Lee--Zhang Lemma 2.6(i).  It deliberately separates the generic
well-founded splitting argument from the table-specific proof that a valid
identity has the required matching cut.
-/

def SameContent (left right : Word Nat) : Prop :=
  ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList

/-- A valid identity can be split at every support-disjoint cut of its left
side, with matching valid factors on the right. -/
def OrderedSplitProperty (candidate : FiniteTable) : Prop :=
  ∀ (identity : Identity Nat) (left right : Word Nat),
    identity.SatisfiedBy candidate.semigroup →
    identity.lhs = left ++ right →
    WordDisjoint left right →
    ∃ left' right' : Word Nat,
      identity.rhs = left' ++ right' ∧
      WordDisjoint left' right' ∧
      SameContent left left' ∧
      SameContent right right' ∧
      (Identity.mk left left').SatisfiedBy candidate.semigroup ∧
      (Identity.mk right right').SatisfiedBy candidate.semigroup

/-- A one-letter side of a valid identity cannot change.  This is the base
case left after all support-disjoint cuts have been removed. -/
def SingletonRigidity (candidate : FiniteTable) : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy candidate.semigroup →
    identity.lhs.toList.length = 1 →
    identity.lhs = identity.rhs

theorem eval_constant_idempotent
    (candidate : FiniteTable) (idempotent : Fin candidate.order)
    (idempotent_mul :
      candidate.mul idempotent idempotent = idempotent)
    (word : Word Nat) :
    candidate.semigroup.eval (fun _ => idempotent) word = idempotent := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      induction tail with
      | nil => rfl
      | cons next rest ih =>
          simp only [List.foldl_cons]
          rw [show candidate.semigroup.mul idempotent idempotent = idempotent by
            exact idempotent_mul]
          exact ih

theorem eval_eq_of_agree_on_word
    (candidate : FiniteTable)
    {first second : Nat → Fin candidate.order} {word : Word Nat}
    (agree :
      ∀ letter, letter ∈ word.toList → first letter = second letter) :
    candidate.semigroup.eval first word =
      candidate.semigroup.eval second word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval, Word.toList] at *
      have headAgree : first head = second head :=
        agree head (List.Mem.head tail)
      have tailAgree :
          ∀ letter ∈ tail, first letter = second letter := by
        intro letter member
        exact agree letter (List.Mem.tail head member)
      have foldAgree :
          ∀ (letters : List Nat)
            (leftInitial rightInitial : Fin candidate.order),
            leftInitial = rightInitial →
            (∀ letter ∈ letters, first letter = second letter) →
            letters.foldl
                (fun current letter =>
                  candidate.mul current (first letter))
                leftInitial =
              letters.foldl
                (fun current letter =>
                  candidate.mul current (second letter))
                rightInitial := by
        intro letters
        induction letters with
        | nil =>
            intro leftInitial rightInitial initialEq _
            exact initialEq
        | cons letter rest ih =>
            intro leftInitial rightInitial initialEq valuesAgree
            simp only [List.foldl_cons]
            apply ih
            · rw [initialEq,
                valuesAgree letter (List.Mem.head rest)]
            · intro value member
              exact valuesAgree value (List.Mem.tail letter member)
      exact foldAgree tail (first head) (second head)
        headAgree tailAgree

private def swapIdentity (identity : Identity Nat) : Identity Nat :=
  ⟨identity.rhs, identity.lhs⟩

private theorem swapIdentity_satisfiedBy
    {candidate : FiniteTable} {identity : Identity Nat}
    (valid : identity.SatisfiedBy candidate.semigroup) :
    (swapIdentity identity).SatisfiedBy candidate.semigroup := by
  intro valuation
  exact (valid valuation).symm

private theorem word_length_pos (word : Word Nat) :
    0 < word.toList.length := by
  cases word
  simp [Word.toList]

private theorem connected_rhs_of_connected_lhs
    {candidate : FiniteTable}
    (singleton : SingletonRigidity candidate)
    (split : OrderedSplitProperty candidate)
    {identity : Identity Nat}
    (valid : identity.SatisfiedBy candidate.semigroup)
    (leftConnected : Connected identity.lhs) :
    Connected identity.rhs := by
  constructor
  · by_cases long : 2 ≤ identity.rhs.toList.length
    · exact long
    · have rhsLengthOne : identity.rhs.toList.length = 1 := by
        have positive := word_length_pos identity.rhs
        omega
      have swappedEquality :=
        singleton (swapIdentity identity)
          (swapIdentity_satisfiedBy valid) rhsLengthOne
      have rhsEqLhs : identity.rhs = identity.lhs := swappedEquality
      rw [rhsEqLhs]
      exact leftConnected.1
  · rintro ⟨rightLeft, rightRight, rightSplit, rightDisjoint⟩
    rcases split (swapIdentity identity) rightLeft rightRight
        (swapIdentity_satisfiedBy valid) rightSplit rightDisjoint with
      ⟨leftLeft, leftRight, leftSplit, leftDisjoint, _, _, _, _⟩
    apply leftConnected.2
    exact ⟨leftLeft, leftRight, leftSplit, leftDisjoint⟩

private structure ConnectedDecomposition
    (candidate : FiniteTable) (identity : Identity Nat)
    (pieces : List (Identity Nat)) : Prop where
  models : Models candidate.semigroup pieces
  connected :
    ∀ piece, piece ∈ pieces → Connected piece.lhs ∧ Connected piece.rhs
  derives : Derives pieces identity.lhs identity.rhs

private theorem derives_mono
    {source target : List (Identity Nat)} {left right : Word Nat}
    (subset : ∀ identity, identity ∈ source → identity ∈ target)
    (derivation : Derives source left right) :
    Derives target left right :=
  derivation.transport fun identity member =>
    Derives.fromBasis (subset identity member)

private theorem exists_connected_decomposition
    {candidate : FiniteTable}
    (singleton : SingletonRigidity candidate)
    (split : OrderedSplitProperty candidate)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy candidate.semigroup) :
    ∃ pieces, ConnectedDecomposition candidate identity pieces := by
  classical
  let targetLength := identity.lhs.toList.length
  have inductionStatement :
      ∀ length,
        (∀ smaller < length,
          ∀ (current : Identity Nat),
            current.lhs.toList.length = smaller →
            current.SatisfiedBy candidate.semigroup →
            ∃ pieces,
              ConnectedDecomposition candidate current pieces) →
        ∀ (current : Identity Nat),
          current.lhs.toList.length = length →
          current.SatisfiedBy candidate.semigroup →
          ∃ pieces,
            ConnectedDecomposition candidate current pieces := by
    intro length smaller current lengthEq currentValid
    by_cases lengthOne : length = 1
    · have currentLengthOne : current.lhs.toList.length = 1 := by
        omega
      have currentEq := singleton current currentValid currentLengthOne
      refine ⟨[], ?_⟩
      refine
        { models := ?_,
          connected := ?_,
          derives := ?_ }
      · intro piece member
        simp at member
      · intro piece member
        simp at member
      · rw [currentEq]
        exact Derives.refl current.rhs
    · by_cases leftConnected : Connected current.lhs
      · have rightConnected :=
          connected_rhs_of_connected_lhs singleton split
            currentValid leftConnected
        refine ⟨[current], ?_⟩
        refine
          { models := ?_,
            connected := ?_,
            derives := ?_ }
        · intro piece member
          simp only [List.mem_singleton] at member
          subst piece
          exact currentValid
        · intro piece member
          simp only [List.mem_singleton] at member
          subst piece
          exact ⟨leftConnected, rightConnected⟩
        · exact Derives.fromBasis (by simp)
      · have currentLong : 2 ≤ current.lhs.toList.length := by
          have positive := word_length_pos current.lhs
          omega
        have disconnected : Disconnected current.lhs := by
          by_cases hasSplit : Disconnected current.lhs
          · exact hasSplit
          · exact False.elim (leftConnected ⟨currentLong, hasSplit⟩)
        rcases disconnected with
          ⟨left, right, leftSplit, leftDisjoint⟩
        rcases split current left right currentValid leftSplit leftDisjoint with
          ⟨left', right', rightSplit, _, _, _, leftValid, rightValid⟩
        let leftIdentity : Identity Nat := ⟨left, left'⟩
        let rightIdentity : Identity Nat := ⟨right, right'⟩
        have leftLength :
            left.toList.length < current.lhs.toList.length := by
          rw [leftSplit, Word.toList_append, List.length_append]
          have positive := word_length_pos right
          omega
        have rightLength :
            right.toList.length < current.lhs.toList.length := by
          rw [leftSplit, Word.toList_append, List.length_append]
          have positive := word_length_pos left
          omega
        have leftLengthEq :
            leftIdentity.lhs.toList.length = left.toList.length := rfl
        have rightLengthEq :
            rightIdentity.lhs.toList.length = right.toList.length := rfl
        rcases smaller left.toList.length (by omega) leftIdentity
            leftLengthEq leftValid with
          ⟨leftPieces, leftDecomposition⟩
        rcases smaller right.toList.length (by omega) rightIdentity
            rightLengthEq rightValid with
          ⟨rightPieces, rightDecomposition⟩
        refine ⟨leftPieces ++ rightPieces, ?_⟩
        refine
          { models := ?_,
            connected := ?_,
            derives := ?_ }
        · intro piece member
          rcases List.mem_append.mp member with member | member
          · exact leftDecomposition.models piece member
          · exact rightDecomposition.models piece member
        · intro piece member
          rcases List.mem_append.mp member with member | member
          · exact leftDecomposition.connected piece member
          · exact rightDecomposition.connected piece member
        · have leftDerives :
              Derives (leftPieces ++ rightPieces) left left' :=
            derives_mono
              (fun piece member =>
                List.mem_append.mpr (Or.inl member))
              leftDecomposition.derives
          have rightDerives :
              Derives (leftPieces ++ rightPieces) right right' :=
            derives_mono
              (fun piece member =>
                List.mem_append.mpr (Or.inr member))
              rightDecomposition.derives
          rw [leftSplit, rightSplit]
          exact Derives.trans
            (Derives.appendRight leftDerives right)
            (Derives.prepend left' rightDerives)
  exact
    Nat.strongRecOn
      (motive := fun length =>
        ∀ (current : Identity Nat),
          current.lhs.toList.length = length →
          current.SatisfiedBy candidate.semigroup →
          ∃ pieces,
            ConnectedDecomposition candidate current pieces)
      targetLength inductionStatement identity rfl valid

/-- The generic finite-support connected reduction. -/
theorem restrictedBasisReduction_of_orderedSplit
    (candidate : FiniteTable)
    (singleton : SingletonRigidity candidate)
    (split : OrderedSplitProperty candidate) :
    RestrictedBasisReduction candidate Connected := by
  refine ⟨?_⟩
  intro identity valid
  rcases exists_connected_decomposition singleton split identity valid with
    ⟨pieces, decomposition⟩
  exact
    ⟨pieces, decomposition.models, decomposition.connected,
      decomposition.derives⟩

end SemigroupBasis.CoRoots.Order6SporadicSection12

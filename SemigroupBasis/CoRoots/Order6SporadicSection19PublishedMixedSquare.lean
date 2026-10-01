import SemigroupBasis.CoRoots.Order6SporadicSection19Presentation

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare

/-- Possible products of nonempty words over the two idempotent values. -/
def BinaryState (value : Fin 6) : Prop :=
  value = 0 ∨ value = 3 ∨ value = 4 ∨ value = 5

/-- The two nonnilpotent outputs have unique binary predecessors. -/
theorem binary_transition : ∀ initial letter : Fin 6,
    BinaryState initial → (letter = 4 ∨ letter = 5) →
    BinaryState (mul initial letter) ∧
      (mul initial letter = 4 → initial = 4 ∧ letter = 4) ∧
      (mul initial letter = 5 → initial = 5 ∧ letter = 5) := by
  unfold BinaryState
  decide

/-- An unrestricted fold invariant, with no bound on the input list. -/
theorem binary_fold_profile (valuation : α → Fin 6) (letters : List α)
    (initial : Fin 6) (initialState : BinaryState initial)
    (binary : ∀ x ∈ letters, valuation x = 4 ∨ valuation x = 5) :
    BinaryState (letters.foldl (fun acc x => mul acc (valuation x)) initial) ∧
      (letters.foldl (fun acc x => mul acc (valuation x)) initial = 4 →
        initial = 4 ∧ ∀ x ∈ letters, valuation x = 4) ∧
      (letters.foldl (fun acc x => mul acc (valuation x)) initial = 5 →
        initial = 5 ∧ ∀ x ∈ letters, valuation x = 5) := by
  induction letters generalizing initial with
  | nil =>
      refine ⟨initialState, ?_, ?_⟩
      · intro same
        exact ⟨same, fun x member => False.elim (List.not_mem_nil member)⟩
      · intro same
        exact ⟨same, fun x member => False.elim (List.not_mem_nil member)⟩
  | cons letter rest ih =>
      have firstBinary : valuation letter = 4 ∨ valuation letter = 5 :=
        binary letter (List.mem_cons_self)
      have restBinary : ∀ x ∈ rest, valuation x = 4 ∨ valuation x = 5 := by
        intro x member
        exact binary x (List.mem_cons_of_mem letter member)
      obtain ⟨nextState, predecessor4, predecessor5⟩ :=
        binary_transition initial (valuation letter) initialState firstBinary
      obtain ⟨finalState, final4, final5⟩ :=
        ih (mul initial (valuation letter)) nextState restBinary
      refine ⟨finalState, ?_, ?_⟩
      · intro same
        obtain ⟨next4, rest4⟩ := final4 same
        obtain ⟨initial4, letter4⟩ := predecessor4 next4
        refine ⟨initial4, ?_⟩
        intro x member
        rcases List.mem_cons.mp member with headEq | tailMem
        · rw [headEq]
          exact letter4
        · exact rest4 x tailMem
      · intro same
        obtain ⟨next5, rest5⟩ := final5 same
        obtain ⟨initial5, letter5⟩ := predecessor5 next5
        refine ⟨initial5, ?_⟩
        intro x member
        rcases List.mem_cons.mp member with headEq | tailMem
        · rw [headEq]
          exact letter5
        · exact rest5 x tailMem

/-- The fold invariant is stated on the actual frozen carrier's word evaluator. -/
theorem binary_word_profile (valuation : α → Fin 6) (word : Word α)
    (binary : ∀ x ∈ word.toList, valuation x = 4 ∨ valuation x = 5) :
    BinaryState (table.semigroup.eval valuation word) ∧
      (table.semigroup.eval valuation word = (4 : Fin 6) →
        ∀ x ∈ word.toList, valuation x = 4) ∧
      (table.semigroup.eval valuation word = (5 : Fin 6) →
        ∀ x ∈ word.toList, valuation x = 5) := by
  have headBinary : valuation word.head = 4 ∨ valuation word.head = 5 :=
    binary word.head (List.mem_cons_self)
  have headState : BinaryState (valuation word.head) := by
    rcases headBinary with four | five
    · exact Or.inr (Or.inr (Or.inl four))
    · exact Or.inr (Or.inr (Or.inr five))
  have tailBinary : ∀ x ∈ word.tail, valuation x = 4 ∨ valuation x = 5 := by
    intro x member
    exact binary x (List.mem_cons_of_mem word.head member)
  obtain ⟨finalState, final4, final5⟩ :=
    binary_fold_profile valuation word.tail (valuation word.head) headState tailBinary
  refine ⟨finalState, ?_, ?_⟩
  · intro same x member
    obtain ⟨head4, tail4⟩ := final4 same
    change x ∈ word.head :: word.tail at member
    rcases List.mem_cons.mp member with headEq | tailMem
    · rw [headEq]
      exact head4
    · exact tail4 x tailMem
  · intro same x member
    obtain ⟨head5, tail5⟩ := final5 same
    change x ∈ word.head :: word.tail at member
    rcases List.mem_cons.mp member with headEq | tailMem
    · rw [headEq]
      exact head5
    · exact tail5 x tailMem

/-- Using both binary values excludes both nonnilpotent outputs. -/
theorem mixed_word_eval (valuation : α → Fin 6) (word : Word α)
    (binary : ∀ x ∈ word.toList, valuation x = 4 ∨ valuation x = 5)
    (hasFour : ∃ x ∈ word.toList, valuation x = 4)
    (hasFive : ∃ x ∈ word.toList, valuation x = 5) :
    table.semigroup.eval valuation word = (0 : Fin 6) ∨
      table.semigroup.eval valuation word = (3 : Fin 6) := by
  obtain ⟨finalState, final4, final5⟩ := binary_word_profile valuation word binary
  rcases finalState with zero | three | four | five
  · exact Or.inl zero
  · exact Or.inr three
  · obtain ⟨x, member, value5⟩ := hasFive
    have impossible : (5 : Fin 6) = 4 := value5.symm.trans (final4 four x member)
    exact False.elim ((by decide : (5 : Fin 6) ≠ 4) impossible)
  · obtain ⟨x, member, value4⟩ := hasFour
    have impossible : (4 : Fin 6) = 5 := value4.symm.trans (final5 five x member)
    exact False.elim ((by decide : (4 : Fin 6) ≠ 5) impossible)

theorem zero_absorbing : ∀ value : Fin 6, mul value 0 = 0 ∧ mul 0 value = 0 := by
  decide

theorem square_of_mixed_value_zero (value : Fin 6) (mixed : value = 0 ∨ value = 3) :
    mul value value = 0 := by
  rcases mixed with rfl | rfl
  · decide
  · decide

/-- Every mixed binary word has zero square, regardless of its length. -/
theorem mixed_square_zero (valuation : α → Fin 6) (word : Word α)
    (binary : ∀ x ∈ word.toList, valuation x = 4 ∨ valuation x = 5)
    (hasFour : ∃ x ∈ word.toList, valuation x = 4)
    (hasFive : ∃ x ∈ word.toList, valuation x = 5) :
    table.semigroup.eval valuation (word ++ word) = (0 : Fin 6) := by
  rw [Semigroup.eval_append]
  exact square_of_mixed_value_zero _ (mixed_word_eval valuation word binary hasFour hasFive)

/-- Arbitrary left/right contexts cannot erase the mixed square's zero value. -/
theorem mixed_square_in_context (valuation : α → Fin 6) (word left right : Word α)
    (binary : ∀ x ∈ word.toList, valuation x = 4 ∨ valuation x = 5)
    (hasFour : ∃ x ∈ word.toList, valuation x = 4)
    (hasFive : ∃ x ∈ word.toList, valuation x = 5) :
    table.semigroup.eval valuation (left ++ ((word ++ word) ++ right)) = (0 : Fin 6) := by
  rw [Semigroup.eval_append, Semigroup.eval_append,
    mixed_square_zero valuation word binary hasFour hasFive]
  change mul (table.semigroup.eval valuation left)
    (mul 0 (table.semigroup.eval valuation right)) = 0
  rw [(zero_absorbing (table.semigroup.eval valuation right)).2,
    (zero_absorbing (table.semigroup.eval valuation left)).1]

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare.binary_transition
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare.binary_fold_profile
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare.binary_word_profile
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare.mixed_word_eval
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare.zero_absorbing
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare.square_of_mixed_value_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare.mixed_square_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MixedSquare.mixed_square_in_context

import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedMixedSquare
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedCanonicalPresentation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation

open CanonicalPresentation MixedSquare

theorem zero_eval_append_left (valuation : α → Fin 6) (piece right : Word α)
    (vanishes : table.semigroup.eval valuation piece = (0 : Fin 6)) :
    table.semigroup.eval valuation (piece ++ right) = (0 : Fin 6) := by
  rw [Semigroup.eval_append]
  change mul (table.semigroup.eval valuation piece)
    (table.semigroup.eval valuation right) = (0 : Fin 6)
  rw [vanishes]
  exact (zero_absorbing (table.semigroup.eval valuation right)).2

theorem zero_eval_append_right (valuation : α → Fin 6) (left piece : Word α)
    (vanishes : table.semigroup.eval valuation piece = (0 : Fin 6)) :
    table.semigroup.eval valuation (left ++ piece) = (0 : Fin 6) := by
  rw [Semigroup.eval_append]
  change mul (table.semigroup.eval valuation left)
    (table.semigroup.eval valuation piece) = (0 : Fin 6)
  rw [vanishes]
  exact (zero_absorbing (table.semigroup.eval valuation left)).1

/-- A literal zero-valued factor annihilates the whole word. Both context
lists may be empty; no identity element or new evaluator is introduced. -/
theorem literal_factor_zero (valuation : α → Fin 6) (word piece : Word α)
    (before after : List α)
    (literal : word.toList = before ++ (piece.toList ++ after))
    (vanishes : table.semigroup.eval valuation piece = (0 : Fin 6)) :
    table.semigroup.eval valuation word = (0 : Fin 6) := by
  cases before with
  | nil =>
      cases after with
      | nil =>
          have same : word = piece := Word.toList_injective
            (literal.trans (List.append_nil piece.toList))
          rw [same]
          exact vanishes
      | cons rightHead rightTail =>
          let rightWord : Word α := ⟨rightHead, rightTail⟩
          have same : word = piece ++ rightWord := Word.toList_injective (by
            rw [Word.toList_append]
            exact literal)
          rw [same]
          exact zero_eval_append_left valuation piece rightWord vanishes
  | cons leftHead leftTail =>
      let leftWord : Word α := ⟨leftHead, leftTail⟩
      cases after with
      | nil =>
          have same : word = leftWord ++ piece := Word.toList_injective (by
            rw [Word.toList_append]
            exact literal.trans (congrArg (fun tail : List α => leftWord.toList ++ tail)
              (List.append_nil piece.toList)))
          rw [same]
          exact zero_eval_append_right valuation leftWord piece vanishes
      | cons rightHead rightTail =>
          let rightWord : Word α := ⟨rightHead, rightTail⟩
          have same : word = leftWord ++ (piece ++ rightWord) := Word.toList_injective (by
            rw [Word.toList_append, Word.toList_append]
            exact literal)
          rw [same]
          exact zero_eval_append_right valuation leftWord (piece ++ rightWord)
            (zero_eval_append_left valuation piece rightWord vanishes)

/-- The mixed-square theorem now applies to any actual literal occurrence,
including occurrences touching either or both ends of the target word. -/
theorem mixed_square_factor_zero (valuation : α → Fin 6) (word root : Word α)
    (before after : List α)
    (literal : word.toList = before ++ ((root ++ root).toList ++ after))
    (binary : ∀ x ∈ root.toList, valuation x = 4 ∨ valuation x = 5)
    (hasFour : ∃ x ∈ root.toList, valuation x = 4)
    (hasFive : ∃ x ∈ root.toList, valuation x = 5) :
    table.semigroup.eval valuation word = (0 : Fin 6) :=
  literal_factor_zero valuation word (root ++ root) before after literal
    (mixed_square_zero valuation root binary hasFour hasFive)

/-- Nonvacuous Family perfection supplies the occurrence; Form is unchanged
and no extra occurrence predicate is postulated. -/
theorem form_root_factor (word : Word Nat) (form : Form word)
    (root : Word Nat) (rootMember : root ∈ form.roots) :
    ∃ before after : List Nat,
      word.toList = before ++ ((root ++ root).toList ++ after) :=
  BlockAlignment.canonical_perfect_literal_factor root word
    (form.family.2 root rootMember).2

theorem form_mixed_root_zero (valuation : Nat → Fin 6) (word : Word Nat)
    (form : Form word) (root : Word Nat) (rootMember : root ∈ form.roots)
    (binary : ∀ x ∈ root.toList, valuation x = 4 ∨ valuation x = 5)
    (hasFour : ∃ x ∈ root.toList, valuation x = 4)
    (hasFive : ∃ x ∈ root.toList, valuation x = 5) :
    table.semigroup.eval valuation word = (0 : Fin 6) := by
  obtain ⟨before, after, literal⟩ := form_root_factor word form root rootMember
  exact mixed_square_factor_zero valuation word root before after literal binary hasFour hasFive

/-- A nonzero source value separates it from a canonical target containing
a mixed root, for the SAME explicitly supplied valuation. -/
theorem form_mixed_root_separates (valuation : Nat → Fin 6) (source target : Word Nat)
    (form : Form target) (root : Word Nat) (rootMember : root ∈ form.roots)
    (binary : ∀ x ∈ root.toList, valuation x = 4 ∨ valuation x = 5)
    (hasFour : ∃ x ∈ root.toList, valuation x = 4)
    (hasFive : ∃ x ∈ root.toList, valuation x = 5)
    (sourceNonzero : table.semigroup.eval valuation source ≠ (0 : Fin 6)) :
    table.semigroup.eval valuation source ≠ table.semigroup.eval valuation target := by
  intro same
  exact sourceNonzero (same.trans
    (form_mixed_root_zero valuation target form root rootMember binary hasFour hasFive))

/-- At any nonzero valuation of an actual canonical word, each root whose
letters take values 4 or 5 is uniformly 4 or uniformly 5. -/
theorem form_nonzero_root_uniform (valuation : Nat → Fin 6) (word : Word Nat)
    (form : Form word) (root : Word Nat) (rootMember : root ∈ form.roots)
    (binary : ∀ x ∈ root.toList, valuation x = 4 ∨ valuation x = 5)
    (nonzero : table.semigroup.eval valuation word ≠ (0 : Fin 6)) :
    (∀ x ∈ root.toList, valuation x = 4) ∨
      (∀ x ∈ root.toList, valuation x = 5) := by
  obtain ⟨before, after, literal⟩ := form_root_factor word form root rootMember
  have excludesMixedValue
      (mixed : table.semigroup.eval valuation root = (0 : Fin 6) ∨
        table.semigroup.eval valuation root = (3 : Fin 6)) : False := by
    have squareZero : table.semigroup.eval valuation (root ++ root) = (0 : Fin 6) := by
      rw [Semigroup.eval_append]
      exact square_of_mixed_value_zero _ mixed
    exact nonzero (literal_factor_zero valuation word (root ++ root) before after literal squareZero)
  obtain ⟨finalState, final4, final5⟩ := binary_word_profile valuation root binary
  rcases finalState with zero | three | four | five
  · exact False.elim (excludesMixedValue (Or.inl zero))
  · exact False.elim (excludesMixedValue (Or.inr three))
  · exact Or.inl (final4 four)
  · exact Or.inr (final5 five)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation.zero_eval_append_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation.zero_eval_append_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation.literal_factor_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation.mixed_square_factor_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation.form_root_factor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation.form_mixed_root_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation.form_mixed_root_separates
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.RootFactorAnnihilation.form_nonzero_root_uniform

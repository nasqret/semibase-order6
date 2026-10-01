import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSimpleMarkerRootRange

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue

open CanonicalPresentation SimpleMarkerRootRange

/-- Uniform nonempty words evaluate to an idempotent value. The proof uses
the standard-library fold rule, not a new run or fold helper. -/
theorem uniform_word_value (G : Semigroup S) (valuation : α → S)
    (word : Word α) (value : S) (idempotent : G.mul value value = value)
    (uniform : ∀ x ∈ word.toList, valuation x = value) :
    G.eval valuation word = value := by
  have initial : valuation word.head = value := uniform word.head List.mem_cons_self
  refine List.foldlRecOn (motive := fun result : S => result = value)
    word.tail (fun acc x => G.mul acc (valuation x)) initial ?_
  intro acc same x member
  change G.mul acc (valuation x) = value
  rw [same, uniform x (List.mem_cons_of_mem word.head member)]
  exact idempotent

theorem fives_value (valuation : α → Fin 6) (word : Word α)
    (fives : ∀ x ∈ word.toList, valuation x = 5) :
    table.semigroup.eval valuation word = (5 : Fin 6) :=
  uniform_word_value table.semigroup valuation word (5 : Fin 6) (by decide) fives

theorem fours_value (valuation : α → Fin 6) (word : Word α)
    (fours : ∀ x ∈ word.toList, valuation x = 4) :
    table.semigroup.eval valuation word = (4 : Fin 6) :=
  uniform_word_value table.semigroup valuation word (4 : Fin 6) (by decide) fours

/-- The nonempty marker word has value2 even when the final5-list is empty. -/
theorem marker_fives_value (valuation : α → Fin 6) (marker : α) (after : List α)
    (markerTwo : valuation marker = 2)
    (afterFive : ∀ x ∈ after, valuation x = 5) :
    table.semigroup.eval valuation (⟨marker, after⟩ : Word α) = (2 : Fin 6) := by
  refine List.foldlRecOn (motive := fun result : Fin 6 => result = (2 : Fin 6))
    after (fun acc x => mul acc (valuation x)) markerTwo ?_
  intro acc same x member
  change mul acc (valuation x) = (2 : Fin 6)
  rw [same, afterFive x member]
  decide

/-- An unrestricted supplied-valuation block pattern has value1. It does not
define a detector or assert that the canonical cut has this pattern. -/
theorem source_block_value (valuation : α → Fin 6) (source left middle : Word α)
    (marker : α) (after : List α)
    (literal : source.toList = left.toList ++ (middle.toList ++ marker :: after))
    (leftFive : ∀ x ∈ left.toList, valuation x = 5)
    (middleFour : ∀ x ∈ middle.toList, valuation x = 4)
    (markerTwo : valuation marker = 2)
    (afterFive : ∀ x ∈ after, valuation x = 5) :
    table.semigroup.eval valuation source = (1 : Fin 6) := by
  let markerWord : Word α := ⟨marker, after⟩
  have words : source = left ++ (middle ++ markerWord) := Word.toList_injective (by
    rw [Word.toList_append, Word.toList_append]
    exact literal)
  have leftValue := fives_value valuation left leftFive
  have middleValue := fours_value valuation middle middleFour
  have markerValue : table.semigroup.eval valuation markerWord = (2 : Fin 6) :=
    marker_fives_value valuation marker after markerTwo afterFive
  rw [words, Semigroup.eval_append, Semigroup.eval_append, leftValue, middleValue, markerValue]
  change mul (5 : Fin 6) (mul (4 : Fin 6) (2 : Fin 6)) = (1 : Fin 6)
  decide

theorem source_block_nonzero (valuation : α → Fin 6) (source left middle : Word α)
    (marker : α) (after : List α)
    (literal : source.toList = left.toList ++ (middle.toList ++ marker :: after))
    (leftFive : ∀ x ∈ left.toList, valuation x = 5)
    (middleFour : ∀ x ∈ middle.toList, valuation x = 4)
    (markerTwo : valuation marker = 2)
    (afterFive : ∀ x ∈ after, valuation x = 5) :
    table.semigroup.eval valuation source ≠ (0 : Fin 6) := by
  rw [source_block_value valuation source left middle marker after
    literal leftFive middleFour markerTwo afterFive]
  decide

/-- Compose the new source algebra with the actual target-root interface.
The valuation and its literal source shape are still explicit inputs. -/
theorem source_blocks_split_root_separates (valuation : Nat → Fin 6)
    (source target left middle : Word Nat) (marker : Nat) (after : List Nat)
    (literal : source.toList = left.toList ++ (middle.toList ++ marker :: after))
    (leftFive : ∀ x ∈ left.toList, valuation x = 5)
    (middleFour : ∀ x ∈ middle.toList, valuation x = 4)
    (markerTwo : valuation marker = 2)
    (afterFive : ∀ x ∈ after, valuation x = 5)
    (form : Form target) (simple : target.toList.count marker = 1)
    (offMarker : ∀ x, x ≠ marker → valuation x = 4 ∨ valuation x = 5)
    (root : Word Nat) (rootMember : root ∈ form.roots)
    (x y : Nat) (inX : x ∈ root.toList) (inY : y ∈ root.toList)
    (valueX : valuation x = 4) (valueY : valuation y = 5) :
    table.semigroup.eval valuation source ≠ table.semigroup.eval valuation target :=
  simple_marker_split_root_separates valuation source target form marker simple offMarker
    root rootMember x y inX inY valueX valueY
    (source_block_nonzero valuation source left middle marker after
      literal leftFive middleFour markerTwo afterFive)

/-- Equal evaluation to this source pattern forces target-root value agreement,
without postulating root-partition equality or a semantic Form field. -/
theorem source_blocks_equal_target_values (valuation : Nat → Fin 6)
    (source target left middle : Word Nat) (marker : Nat) (after : List Nat)
    (literal : source.toList = left.toList ++ (middle.toList ++ marker :: after))
    (leftFive : ∀ x ∈ left.toList, valuation x = 5)
    (middleFour : ∀ x ∈ middle.toList, valuation x = 4)
    (markerTwo : valuation marker = 2)
    (afterFive : ∀ x ∈ after, valuation x = 5)
    (form : Form target) (simple : target.toList.count marker = 1)
    (offMarker : ∀ x, x ≠ marker → valuation x = 4 ∨ valuation x = 5)
    (same : table.semigroup.eval valuation source = table.semigroup.eval valuation target)
    (root : Word Nat) (rootMember : root ∈ form.roots)
    (x y : Nat) (inX : x ∈ root.toList) (inY : y ∈ root.toList) :
    valuation x = valuation y := by
  have sourceNonzero := source_block_nonzero valuation source left middle marker after
    literal leftFive middleFour markerTwo afterFive
  have targetNonzero : table.semigroup.eval valuation target ≠ (0 : Fin 6) := by
    intro targetZero
    exact sourceNonzero (same.trans targetZero)
  exact simple_marker_root_values_agree valuation target form marker simple offMarker
    root rootMember targetNonzero x y inX inY

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue.uniform_word_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue.fives_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue.fours_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue.marker_fives_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue.source_block_value
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue.source_block_nonzero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue.source_blocks_split_root_separates
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SourceBlockValue.source_blocks_equal_target_values

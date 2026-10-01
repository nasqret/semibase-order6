import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedConnectedTerminalEndpoints
import SemigroupBasis.Examples.ConnectedComponentFourSemantics

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization

open Examples MaximalFactors RootFamily RootBlockPartition SimpleFactorInvariant
open MaximalSimpleAlignment TerminalRepeatBoundary ConnectedTerminalEndpoints

/-- Actual zero-based S4_70 -> frozen C8 map. Displayed paper labels are not
used as our table labels. -/
def includeFour (value : Fin 4) : Fin 6 :=
  match value.val with
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | _ => 4

theorem includeFour_mul (left right : Fin 4) :
    includeFour (connectedComponentFour.mul left right) =
      table.mul (includeFour left) (includeFour right) := by
  have concrete : ∀ a b : Fin 4,
      includeFour (connectedComponentFour.mul a b) =
        table.mul (includeFour a) (includeFour b) := by decide
  exact concrete left right

theorem includeFour_injective : Function.Injective includeFour := by
  have concrete : ∀ a b : Fin 4, includeFour a = includeFour b → a = b := by decide
  exact concrete

private theorem includeFour_fold (valuation : Nat → Fin 4)
    (letters : List Nat) (initial : Fin 4) :
    includeFour (letters.foldl (fun state letter =>
      connectedComponentFour.mul state (valuation letter)) initial) =
    letters.foldl (fun state letter => table.mul state (includeFour (valuation letter)))
      (includeFour initial) := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter rest ih =>
    simp only [List.foldl_cons]
    rw [ih, includeFour_mul]

/-- The finite map is lifted to arbitrary nonempty words. -/
theorem includeFour_eval (word : Word Nat) (valuation : Nat → Fin 4) :
    includeFour (connectedComponentFour.semigroup.eval valuation word) =
      table.semigroup.eval (fun letter => includeFour (valuation letter)) word := by
  cases word with
  | mk first rest => exact includeFour_fold valuation rest (valuation first)

theorem derives_small_eval (source target : Word Nat)
    (derived : Derives basis source target) (valuation : Nat → Fin 4) :
    connectedComponentFour.semigroup.eval valuation source =
      connectedComponentFour.semigroup.eval valuation target := by
  apply includeFour_injective
  calc
    includeFour (connectedComponentFour.semigroup.eval valuation source) =
        table.semigroup.eval (fun letter => includeFour (valuation letter)) source :=
      includeFour_eval source valuation
    _ = table.semigroup.eval (fun letter => includeFour (valuation letter)) target :=
      derived.sound SemigroupBasis.CoRoots.Order6SporadicSection19.Published.models
        (fun letter => includeFour (valuation letter))
    _ = includeFour (connectedComponentFour.semigroup.eval valuation target) :=
      (includeFour_eval target valuation).symm

/-- Any disjoint nonempty target cut transfers back through the existing
exact S4_70 detector, contradicting actual source connectedness. -/
theorem derives_no_disjoint_cut (source target : Word Nat)
    (derived : Derives basis source target) (connected : Connected source) :
    ¬ ∃ left right : Word Nat, target = left ++ right ∧ Apart left right := by
  rintro ⟨left, right, split, apart⟩
  have targetCut : connectedComponentFourPrefixUnionCut left.toList target.toList := by
    refine ⟨left.toList, right.toList, ?_, piece_nonempty left, piece_nonempty right, ?_, ?_⟩
    · rw [split, Word.toList_append]
    · intro letter
      exact Iff.rfl
    · intro letter inLeft inRight
      exact apart letter inLeft inRight
  have covered : ∀ letter, letter ∈ left.toList → letter ∈ target.toList := by
    intro letter member
    rw [split, Word.toList_append]
    exact List.mem_append.mpr (Or.inl member)
  have equalReverse : ∀ valuation : Nat → Fin 4,
      connectedComponentFour.semigroup.eval valuation target =
        connectedComponentFour.semigroup.eval valuation source := by
    intro valuation
    exact (derives_small_eval source target derived valuation).symm
  have sourceCut :=
    (connectedComponentFourEqualEval_prefixUnionCut_iff target source equalReverse
      left.toList covered).mp targetCut
  obtain ⟨before, after, literal, beforeNonempty, afterNonempty, _, disjoint⟩ := sourceCut
  obtain ⟨letter, inBefore, inAfter⟩ := connected_cut_overlap source connected
    before after beforeNonempty afterNonempty literal
  exact disjoint letter inBefore inAfter

/-- Non-singleton length is discharged from a genuine repeated output
letter. The no-cut conclusion is proved through the faithful detector. -/
theorem connected_of_derives_and_repeated (source target : Word Nat)
    (derived : Derives basis source target) (connected : Connected source)
    (letter : Nat) (repeated : 2 ≤ target.toList.count letter) : Connected target := by
  refine ⟨?_, derives_no_disjoint_cut source target derived connected⟩
  exact Nat.le_trans repeated (List.count_le_length (a := letter) (l := target.toList))

/-- The chosen literal38 normalizer really preserves connectedness and hence
has matching endpoint root squares. No output-connectedness premise, finite
screen bound, semantic-completeness premise or canonical-comparison axiom
is supplied. All prior maximal simple and repeat-boundary data are retained. -/
theorem normalize_connected_with_endpoints (word : Word Nat) (connected : Connected word) :
    ∃ normal : Word Nat, ∃ roots : List (Word Nat), ∃ pieces : List (Word Nat),
      Derives basis word normal ∧ Connected normal ∧ Family roots normal ∧
      Terminal roots normal ∧
      (∀ value, Covered roots value ↔ 2 ≤ word.toList.count value) ∧
      (∀ value, Covered roots value ↔ 2 ≤ normal.toList.count value) ∧
      SquarePartition roots normal pieces ∧
      NegativeParts (repeatedTag normal) pieces = simpleFactors normal ∧
      NegativeParts (repeatedTag normal) pieces = simpleFactors word ∧
      (∀ part ∈ pieces, (∃ root ∈ roots, part = root ++ root) ∨
        (∀ value ∈ part.toList,
          word.toList.count value = 1 ∧ normal.toList.count value = 1)) ∧
      RepeatBoundary roots pieces ∧
      (∃ root ∈ roots, ∃ tail initial : List (Word Nat),
        pieces = (root ++ root) :: tail ∧ pieces = initial ++ [root ++ root]) := by
  obtain ⟨normal, roots, pieces, derived, family, terminal, original, current,
    partition, alignedNormal, alignedOriginal, kinds, repeatBoundary⟩ := normalize_with_repeat_boundary word
  have repeatedInput : 2 ≤ word.toList.count word.head := connected_head_repeated word connected
  have repeatedOutput : 2 ≤ normal.toList.count word.head :=
    (current word.head).mp ((original word.head).mpr repeatedInput)
  have outputConnected : Connected normal :=
    connected_of_derives_and_repeated word normal derived connected word.head repeatedOutput
  refine ⟨normal, roots, pieces, derived, outputConnected, family, terminal, original, current,
    partition, alignedNormal, alignedOriginal, kinds, repeatBoundary, ?_⟩
  exact connected_terminal_endpoints roots normal pieces outputConnected family terminal partition current

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization.includeFour_mul
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization.includeFour_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization.includeFour_eval
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization.derives_small_eval
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization.derives_no_disjoint_cut
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization.connected_of_derives_and_repeated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.ConnectedNormalization.normalize_connected_with_endpoints

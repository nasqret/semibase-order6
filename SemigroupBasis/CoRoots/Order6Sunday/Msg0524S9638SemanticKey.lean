import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9643SemanticKey

/-! S9638 has a left-regular-band retract. Its arbitrary-word semantic key
is capped length, first-occurrence order and the unique initial marker.
Generic finite decoding and length facts are reused, not S9643's theory. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638SemanticKey

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638CommonIdeal
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey
  (snoc toList_snoc snoc_exists snoc_long depth depthValue_injective allLow_eq_true)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey (UniqueInitial)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9643SemanticKey
  (embedValue collapse fourFlag decode decode_collapse eval_long_range long_value_determined eval_all_two)

def bandEmbedding : Embedding leftRegularBandThree.semigroup (table 0).semigroup where
  toFun := embedValue
  map_mul := by decide
  injective := by
    intro a b same
    exact (by decide : ∀ a b : Fin 3, embedValue a = embedValue b → a = b) a b same

def bandProjection : Hom (table 0).semigroup leftRegularBandThree.semigroup where
  toFun := collapse
  map_mul := by decide

theorem collapse_eval (valuation : α → Fin 6) (word : Word α) :
    collapse (eval 0 valuation word) =
      leftRegularBandThree.semigroup.eval (fun x => collapse (valuation x)) word :=
  bandProjection.map_eval valuation word

theorem firstOrder_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy (table 0).semigroup) :
    firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    _ (bandEmbedding.pullback_identity (Identity.mk left right) valid)

theorem band_valid_of_firstOrder (left right : Word Nat)
    (order : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList) :
    (Identity.mk left right).SatisfiedBy leftRegularBandThree.semigroup := by
  have leftNormal := lrbDerivesNormal left
  have rightNormal := lrbDerivesNormal right
  cases normal : firstOccurrenceSequence left.toList with
  | nil =>
      rw [normal] at leftNormal
      exact False.elim leftNormal
  | cons head tail =>
      have rightSequence : firstOccurrenceSequence right.toList = head :: tail :=
        order.symm.trans normal
      rw [normal] at leftNormal
      rw [rightSequence] at rightNormal
      exact (leftNormal.trans rightNormal.symm).sound leftRegularBandThreeBasis_models

theorem first_of_firstOrder (a b : Nat) (left right : List Nat)
    (order : firstOccurrenceSequence (a :: left) = firstOccurrenceSequence (b :: right)) :
    a = b := by
  change a :: _ = b :: _ at order
  exact (List.cons.inj order).1

theorem support_of_firstOrder (left right : List Nat)
    (order : firstOccurrenceSequence left = firstOccurrenceSequence right) :
    ∀ marker, marker ∈ left ↔ marker ∈ right := by
  intro marker
  have same : marker ∈ firstOccurrenceSequence left ↔ marker ∈ firstOccurrenceSequence right := by
    rw [order]
  simpa only [mem_firstOccurrenceSequence_iff] using same

theorem collapse_eq_of_firstOrder (valuation : Nat → Fin 6) (left right : Word Nat)
    (order : firstOccurrenceSequence left.toList = firstOccurrenceSequence right.toList) :
    collapse (eval 0 valuation left) = collapse (eval 0 valuation right) := by
  rw [collapse_eval, collapse_eval]
  exact band_valid_of_firstOrder left right order (fun x => collapse (valuation x))

theorem fourFlag_spec (valuation : α → Fin 6) (word : Word α) :
    fourFlag valuation word = true ↔ eval 0 valuation word = 4 := by
  rw [eval_four_left 0 (by decide)]
  simp [fourFlag, allLow_eq_true]

theorem eval_long_formula (valuation : α → Fin 6) (word : Word α)
    (long : 3 ≤ word.toList.length) :
    eval 0 valuation word = decode
      (leftRegularBandThree.semigroup.eval (fun x => collapse (valuation x)) word)
      (fourFlag valuation word) := by
  have flag : fourFlag valuation word = decide (eval 0 valuation word = 4) := by
    by_cases four : eval 0 valuation word = 4
    · have yes := (fourFlag_spec valuation word).mpr four
      simpa [four] using yes
    · have no : fourFlag valuation word = false := by
        cases value : fourFlag valuation word with
        | false => rfl
        | true => exact False.elim (four ((fourFlag_spec valuation word).mp value))
      simpa [four] using no
  rw [← collapse_eval, flag]
  exact (decode_collapse _ (eval_long_range 0 valuation word long)).symm

theorem four_iff_of_observations (valuation : α → Fin 6) (left right : Word α)
    (support : ∀ x, x ∈ left.toList ↔ x ∈ right.toList)
    (initial : ∀ x, UniqueInitial left x ↔ UniqueInitial right x) :
    eval 0 valuation left = 4 ↔ eval 0 valuation right = 4 := by
  have old := SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey.four_iff_of_observations
    valuation left right support initial
  rw [eval_four_left 1 (by decide), eval_four_left 1 (by decide)] at old
  rw [eval_four_left 0 (by decide), eval_four_left 0 (by decide)]
  exact old

def SameCutKey (left : List Nat) (a : Nat) (right : List Nat) (b : Nat) : Prop :=
  depth left = depth right ∧
  firstOccurrenceSequence (left ++ [a]) = firstOccurrenceSequence (right ++ [b]) ∧
  ∀ x, UniqueInitial (snoc left a) x ↔ UniqueInitial (snoc right b) x

theorem key_of_valid (left right : List Nat) (a b : Nat)
    (valid : (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 0).semigroup) :
    SameCutKey left a right b := by
  have order : firstOccurrenceSequence (left ++ [a]) = firstOccurrenceSequence (right ++ [b]) := by
    simpa only [toList_snoc] using firstOrder_of_valid (snoc left a) (snoc right b) valid
  have degree := valid (fun _ => (2 : Fin 6))
  change eval 0 (fun _ => (2 : Fin 6)) (snoc left a) =
    eval 0 (fun _ => (2 : Fin 6)) (snoc right b) at degree
  rw [eval_all_two, eval_all_two] at degree
  exact ⟨depthValue_injective degree, order, initial_marker_of_valid 0 (by decide) _ valid⟩

theorem valid_of_key (left right : List Nat) (a b : Nat) (key : SameCutKey left a right b) :
    (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 0).semigroup := by
  rcases key with ⟨degree, order, initial⟩
  have support := support_of_firstOrder (left ++ [a]) (right ++ [b]) order
  intro valuation
  change eval 0 valuation (snoc left a) = eval 0 valuation (snoc right b)
  cases left with
  | nil =>
      cases right with
      | nil =>
          have same : a = b := first_of_firstOrder a b [] [] order
          subst b
          rfl
      | cons c rest => cases rest <;> simp [depth] at degree
  | cons c rest =>
      cases rest with
      | nil =>
          cases right with
          | nil => simp [depth] at degree
          | cons d rest =>
              cases rest with
              | nil =>
                  have heads : c = d := first_of_firstOrder c d [a] [b] order
                  subst d
                  have finalSame : a = b := by
                    by_cases h : a = c
                    · subst a
                      have present := (support b).mpr (by simp)
                      have bc : b = c := by simpa using present
                      exact bc.symm
                    · have present := (support a).mp (by simp)
                      simpa [h] using present
                  subst b
                  rfl
              | cons e rest => simp [depth] at degree
      | cons d rest =>
          cases right with
          | nil => simp [depth] at degree
          | cons e tail =>
              cases tail with
              | nil => simp [depth] at degree
              | cons f tail =>
                  have content : ∀ x, x ∈ (snoc (c :: d :: rest) a).toList ↔
                      x ∈ (snoc (e :: f :: tail) b).toList := by
                    simpa only [toList_snoc] using support
                  apply long_value_determined
                  · exact eval_long_range 0 valuation _ (snoc_long c d rest a)
                  · exact eval_long_range 0 valuation _ (snoc_long e f tail b)
                  · apply collapse_eq_of_firstOrder
                    simpa only [toList_snoc] using order
                  · exact four_iff_of_observations valuation _ _ content initial

theorem cut_semantic_key_iff (left right : List Nat) (a b : Nat) :
    (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 0).semigroup ↔
      SameCutKey left a right b :=
  ⟨key_of_valid left right a b, valid_of_key left right a b⟩

def SameKey (left right : Word Nat) : Prop :=
  ∃ leftStem a rightStem b, left = snoc leftStem a ∧ right = snoc rightStem b ∧
    SameCutKey leftStem a rightStem b

theorem semantic_key_iff (left right : Word Nat) :
    (Identity.mk left right).SatisfiedBy (table 0).semigroup ↔ SameKey left right := by
  constructor
  · intro valid
    rcases snoc_exists left with ⟨leftStem, a, hl⟩
    rcases snoc_exists right with ⟨rightStem, b, hr⟩
    refine ⟨leftStem, a, rightStem, b, hl, hr, ?_⟩
    rw [hl, hr] at valid
    exact (cut_semantic_key_iff leftStem rightStem a b).mp valid
  · rintro ⟨leftStem, a, rightStem, b, hl, hr, key⟩
    rw [hl, hr]
    exact (cut_semantic_key_iff leftStem rightStem a b).mpr key

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9638SemanticKey

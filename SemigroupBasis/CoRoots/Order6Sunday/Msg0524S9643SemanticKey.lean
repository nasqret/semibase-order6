import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_1089Normalization

/-! S9643 has a right-regular-band retract. Its complete arbitrary-word
criterion is capped length, last-occurrence order and the unique initial
marker. The separate final-letter field below is redundant but convenient. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9643SemanticKey

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638CommonIdeal
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey
  (snoc toList_snoc snoc_exists snoc_long depth depthValue depthValue_injective allLow allLow_eq_true)
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey (UniqueInitial)
open SemigroupBasis.CoRoots.S5_1089
  (lastOccurrenceSequence lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence)

def embedValue (value : Fin 3) : Fin 6 :=
  if value = 0 then 3 else if value = 1 then 0 else 5

def collapse (value : Fin 6) : Fin 3 :=
  if value.val < 3 then 1 else if value = 5 then 2 else 0

def bandEmbedding : Embedding leftRegularBandThree.semigroup.opposite (table 2).semigroup where
  toFun := embedValue
  map_mul := by decide
  injective := by
    intro a b same
    exact (by decide : ∀ a b : Fin 3, embedValue a = embedValue b → a = b) a b same

def bandProjection : Hom (table 2).semigroup leftRegularBandThree.semigroup.opposite where
  toFun := collapse
  map_mul := by decide

theorem projection_embedding : ∀ value : Fin 3, collapse (embedValue value) = value := by decide

theorem collapse_eval (valuation : α → Fin 6) (word : Word α) :
    collapse (eval 2 valuation word) =
      leftRegularBandThree.semigroup.opposite.eval (fun x => collapse (valuation x)) word :=
  bandProjection.map_eval valuation word

theorem lastOrder_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy (table 2).semigroup) :
    lastOccurrenceSequence left.toList = lastOccurrenceSequence right.toList := by
  have bandValid := bandEmbedding.pullback_identity (Identity.mk left right) valid
  have reversedValid := (Identity.satisfiedBy_opposite_iff_reversed
    (Identity.mk left right) leftRegularBandThree.semigroup).mp bandValid
  have first := SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    _ reversedValid
  rw [lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence,
    lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence]
  apply congrArg List.reverse
  simpa only [Identity.reversed, Word.toList_reverse] using first

theorem band_valid_of_lastOrder (left right : Word Nat)
    (order : lastOccurrenceSequence left.toList = lastOccurrenceSequence right.toList) :
    (Identity.mk left right).SatisfiedBy leftRegularBandThree.semigroup.opposite := by
  have sameFirst : firstOccurrenceSequence left.reverse.toList =
      firstOccurrenceSequence right.reverse.toList := by
    have reversed := congrArg List.reverse order
    simpa only [lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence,
      List.reverse_reverse, Word.toList_reverse] using reversed
  apply (Identity.satisfiedBy_opposite_iff_reversed
    (Identity.mk left right) leftRegularBandThree.semigroup).mpr
  have leftNormal := lrbDerivesNormal left.reverse
  have rightNormal := lrbDerivesNormal right.reverse
  cases normal : firstOccurrenceSequence left.reverse.toList with
  | nil =>
      rw [normal] at leftNormal
      exact False.elim leftNormal
  | cons head tail =>
      have rightSequence : firstOccurrenceSequence right.reverse.toList = head :: tail := by
        exact sameFirst.symm.trans normal
      rw [normal] at leftNormal
      rw [rightSequence] at rightNormal
      exact (leftNormal.trans rightNormal.symm).sound leftRegularBandThreeBasis_models

theorem lastOrder_mem (marker : Nat) (letters : List Nat) :
    marker ∈ lastOccurrenceSequence letters ↔ marker ∈ letters := by
  rw [lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence]
  simp only [List.mem_reverse, mem_firstOccurrenceSequence_iff]

theorem last_of_lastOrder (left right : List Nat) (a b : Nat)
    (order : lastOccurrenceSequence (left ++ [a]) = lastOccurrenceSequence (right ++ [b])) :
    a = b := by
  have same := congrArg List.reverse order
  simp only [lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence,
    List.reverse_reverse, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append] at same
  change a :: _ = b :: _ at same
  exact (List.cons.inj same).1

theorem support_of_lastOrder (left right : List Nat)
    (order : lastOccurrenceSequence left = lastOccurrenceSequence right) :
    ∀ marker, marker ∈ left ↔ marker ∈ right := by
  intro marker
  rw [← lastOrder_mem marker left, ← lastOrder_mem marker right, order]

theorem collapse_eq_of_lastOrder (valuation : Nat → Fin 6) (left right : Word Nat)
    (order : lastOccurrenceSequence left.toList = lastOccurrenceSequence right.toList) :
    collapse (eval 2 valuation left) = collapse (eval 2 valuation right) := by
  rw [collapse_eval, collapse_eval]
  exact band_valid_of_lastOrder left right order (fun x => collapse (valuation x))

theorem eval_long_range (family : Fin 4) (valuation : α → Fin 6) (word : Word α)
    (long : 3 ≤ word.toList.length) :
    eval family valuation word = 0 ∨ eval family valuation word = 3 ∨
      eval family valuation word = 4 ∨ eval family valuation word = 5 := by
  by_cases low : Low (eval family valuation word)
  · exact Or.inl (eval_zero_of_low_long family valuation word
      ((eval_low_iff family valuation word).mp low) long)
  · exact Or.inr ((by unfold Low; decide : ∀ value : Fin 6,
      ¬ Low value → value = 3 ∨ value = 4 ∨ value = 5) _ low)

theorem long_value_determined : ∀ (a b : Fin 6),
    (a = 0 ∨ a = 3 ∨ a = 4 ∨ a = 5) →
    (b = 0 ∨ b = 3 ∨ b = 4 ∨ b = 5) →
    collapse a = collapse b → (a = 4 ↔ b = 4) → a = b := by decide

def fourFlag (valuation : α → Fin 6) (word : Word α) : Bool :=
  decide (valuation word.head = 4) && allLow valuation word.tail

theorem fourFlag_spec (valuation : α → Fin 6) (word : Word α) :
    fourFlag valuation word = true ↔ eval 2 valuation word = 4 := by
  rw [eval_four_left 2 (by decide)]
  simp [fourFlag, allLow_eq_true]

def decode (band : Fin 3) (four : Bool) : Fin 6 :=
  if band = 1 then 0 else if band = 2 then 5 else if four = true then 4 else 3

theorem decode_collapse : ∀ value : Fin 6,
    (value = 0 ∨ value = 3 ∨ value = 4 ∨ value = 5) →
    decode (collapse value) (decide (value = 4)) = value := by decide

theorem eval_long_formula (valuation : α → Fin 6) (word : Word α)
    (long : 3 ≤ word.toList.length) :
    eval 2 valuation word = decode
      (leftRegularBandThree.semigroup.opposite.eval (fun x => collapse (valuation x)) word)
      (fourFlag valuation word) := by
  have flag : fourFlag valuation word = decide (eval 2 valuation word = 4) := by
    by_cases four : eval 2 valuation word = 4
    · have yes := (fourFlag_spec valuation word).mpr four
      simpa [four] using yes
    · have no : fourFlag valuation word = false := by
        cases value : fourFlag valuation word with
        | false => rfl
        | true => exact False.elim (four ((fourFlag_spec valuation word).mp value))
      simpa [four] using no
  rw [← collapse_eval, flag]
  exact (decode_collapse _ (eval_long_range 2 valuation word long)).symm

theorem four_iff_of_observations (valuation : α → Fin 6) (left right : Word α)
    (support : ∀ x, x ∈ left.toList ↔ x ∈ right.toList)
    (initial : ∀ x, UniqueInitial left x ↔ UniqueInitial right x) :
    eval 2 valuation left = 4 ↔ eval 2 valuation right = 4 := by
  have old := SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey.four_iff_of_observations
    valuation left right support initial
  rw [eval_four_left 1 (by decide), eval_four_left 1 (by decide)] at old
  rw [eval_four_left 2 (by decide), eval_four_left 2 (by decide)]
  exact old

theorem eval_all_two (family : Fin 4) (stem : List α) (last : α) :
    eval family (fun _ => (2 : Fin 6)) (snoc stem last) = depthValue (depth stem) := by
  cases stem with
  | nil => rfl
  | cons a rest =>
      cases rest with
      | nil =>
          change mul family 2 2 = 1
          exact (by decide : ∀ family : Fin 4, mul family 2 2 = 1) family
      | cons b rest =>
          change eval family (fun _ => (2 : Fin 6)) (snoc (a :: b :: rest) last) = 0
          exact eval_zero_of_low_long family (fun _ => 2) _
            (fun _ _ => by change (2 : Fin 6).val < 3; decide) (snoc_long a b rest last)

def SameCutKey (left : List Nat) (a : Nat) (right : List Nat) (b : Nat) : Prop :=
  depth left = depth right ∧ a = b ∧
  lastOccurrenceSequence (left ++ [a]) = lastOccurrenceSequence (right ++ [b]) ∧
  ∀ x, UniqueInitial (snoc left a) x ↔ UniqueInitial (snoc right b) x

theorem key_of_valid (left right : List Nat) (a b : Nat)
    (valid : (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 2).semigroup) :
    SameCutKey left a right b := by
  have order : lastOccurrenceSequence (left ++ [a]) = lastOccurrenceSequence (right ++ [b]) := by
    simpa only [toList_snoc] using lastOrder_of_valid (snoc left a) (snoc right b) valid
  have degree := valid (fun _ => (2 : Fin 6))
  change eval 2 (fun _ => (2 : Fin 6)) (snoc left a) =
    eval 2 (fun _ => (2 : Fin 6)) (snoc right b) at degree
  rw [eval_all_two, eval_all_two] at degree
  exact ⟨depthValue_injective degree, last_of_lastOrder left right a b order, order,
    initial_marker_of_valid 2 (by decide) _ valid⟩

theorem valid_of_key (left right : List Nat) (a b : Nat) (key : SameCutKey left a right b) :
    (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 2).semigroup := by
  rcases key with ⟨degree, finalSame, order, initial⟩
  subst b
  have support := support_of_lastOrder (left ++ [a]) (right ++ [a]) order
  intro valuation
  change eval 2 valuation (snoc left a) = eval 2 valuation (snoc right a)
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons c rest => cases rest <;> simp [depth] at degree
  | cons c rest =>
      cases rest with
      | nil =>
          cases right with
          | nil => simp [depth] at degree
          | cons d rest =>
              cases rest with
              | nil =>
                  have same : c = d := by
                    by_cases h : c = a
                    · subst c
                      have present := (support d).mpr (by simp)
                      have da : d = a := by simpa using present
                      exact da.symm
                    · have present := (support c).mp (by simp)
                      simpa [h] using present
                  subst d
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
                      x ∈ (snoc (e :: f :: tail) a).toList := by
                    simpa only [toList_snoc] using support
                  apply long_value_determined
                  · exact eval_long_range 2 valuation _ (snoc_long c d rest a)
                  · exact eval_long_range 2 valuation _ (snoc_long e f tail a)
                  · apply collapse_eq_of_lastOrder
                    simpa only [toList_snoc] using order
                  · exact four_iff_of_observations valuation _ _ content initial

theorem cut_semantic_key_iff (left right : List Nat) (a b : Nat) :
    (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 2).semigroup ↔
      SameCutKey left a right b :=
  ⟨key_of_valid left right a b, valid_of_key left right a b⟩

def SameKey (left right : Word Nat) : Prop :=
  ∃ leftStem a rightStem b, left = snoc leftStem a ∧ right = snoc rightStem b ∧
    SameCutKey leftStem a rightStem b

theorem semantic_key_iff (left right : Word Nat) :
    (Identity.mk left right).SatisfiedBy (table 2).semigroup ↔ SameKey left right := by
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

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9643SemanticKey

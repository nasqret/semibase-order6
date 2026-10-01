import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey

/-! Exact semantic criterion for literal S9642 (family index 1).
This reuses only the total word cut and the already proved common ideal and
marker observations. No derivational completeness is imported or assumed. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638CommonIdeal
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey
  (snoc toList_snoc snoc_exists snoc_long depth depthValue depthValue_injective)

def UniqueInitial (word : Word α) (marker : α) : Prop :=
  word.head = marker ∧ marker ∉ word.tail

theorem mul_five : ∀ (a b : Fin 6), mul 1 a b = 5 ↔ b = 5 := by decide

theorem eval_five (valuation : α → Fin 6) (stem : List α) (last : α) :
    eval 1 valuation (snoc stem last) = 5 ↔ valuation last = 5 := by
  cases stem with
  | nil => rfl
  | cons a rest =>
      change eval 1 valuation (Word.mk a rest ++ Word.singleton last) = 5 ↔ _
      rw [eval_snoc, mul_five]

theorem eval_zero_long (valuation : α → Fin 6) (word : Word α)
    (long : 3 ≤ word.toList.length) :
    eval 1 valuation word = 0 ↔ ∀ a ∈ word.toList, Low (valuation a) := by
  constructor
  · intro zero
    apply (eval_low_iff 1 valuation word).mp
    rw [zero]
    unfold Low
    decide
  · intro low
    exact eval_zero_of_low_long 1 valuation word low long

theorem eval_long_range (valuation : α → Fin 6) (word : Word α)
    (long : 3 ≤ word.toList.length) :
    eval 1 valuation word = 0 ∨ eval 1 valuation word = 3 ∨
      eval 1 valuation word = 4 ∨ eval 1 valuation word = 5 := by
  by_cases low : Low (eval 1 valuation word)
  · exact Or.inl ((eval_zero_long valuation word long).mpr
      ((eval_low_iff 1 valuation word).mp low))
  · exact Or.inr ((by unfold Low; decide : ∀ value : Fin 6,
      ¬ Low value → value = 3 ∨ value = 4 ∨ value = 5) _ low)

theorem long_value_determined : ∀ (a b : Fin 6),
    (a = 0 ∨ a = 3 ∨ a = 4 ∨ a = 5) →
    (b = 0 ∨ b = 3 ∨ b = 4 ∨ b = 5) →
    (a = 0 ↔ b = 0) → (a = 4 ↔ b = 4) → (a = 5 ↔ b = 5) → a = b := by decide

noncomputable def longValue (valuation : α → Fin 6) (first : α)
    (tail : List α) (last : α) : Fin 6 := by
  classical
  exact if (∀ x ∈ first :: tail, Low (valuation x)) then 0
    else if valuation last = 5 then 5
    else if valuation first = 4 ∧ (∀ x ∈ tail, Low (valuation x)) then 4 else 3

theorem eval_long_formula (valuation : α → Fin 6) (a b : α)
    (rest : List α) (last : α) :
    eval 1 valuation (snoc (a :: b :: rest) last) =
      longValue valuation a (b :: (rest ++ [last])) last := by
  classical
  unfold longValue
  let word := snoc (a :: b :: rest) last
  have long := snoc_long a b rest last
  by_cases low : ∀ x ∈ a :: b :: (rest ++ [last]), Low (valuation x)
  · rw [if_pos low]
    exact (eval_zero_long valuation word long).mpr low
  · rw [if_neg low]
    by_cases five : valuation last = 5
    · rw [if_pos five]
      exact (eval_five valuation (a :: b :: rest) last).mpr five
    · rw [if_neg five]
      by_cases four : valuation a = 4 ∧ ∀ x ∈ b :: (rest ++ [last]), Low (valuation x)
      · rw [if_pos four]
        exact (eval_four_left 1 (by decide) valuation word).mpr four
      · rw [if_neg four]
        rcases eval_long_range valuation word long with zero | three | isFour | isFive
        · exact False.elim (low ((eval_zero_long valuation word long).mp zero))
        · exact three
        · exact False.elim (four ((eval_four_left 1 (by decide) valuation word).mp isFour))
        · exact False.elim (five ((eval_five valuation (a :: b :: rest) last).mp isFive))

def marker5 [DecidableEq α] (marker a : α) : Fin 6 := if a = marker then 5 else 0

theorem marker5_final [DecidableEq α] (stem : List α) (last marker : α) :
    eval 1 (marker5 marker) (snoc stem last) = 5 ↔ last = marker := by
  rw [eval_five]
  by_cases same : last = marker <;> simp [marker5, same]

theorem eval_all_two (stem : List α) (last : α) :
    eval 1 (fun _ => (2 : Fin 6)) (snoc stem last) = depthValue (depth stem) := by
  cases stem with
  | nil => rfl
  | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b rest =>
          change eval 1 (fun _ => (2 : Fin 6)) (snoc (a :: b :: rest) last) = 0
          exact eval_zero_of_low_long 1 (fun _ => 2) _
            (fun _ _ => by change (2 : Fin 6).val < 3; decide) (snoc_long a b rest last)

theorem support_of_valid [DecidableEq α] (left right : Word α)
    (valid : (Identity.mk left right).SatisfiedBy (table 1).semigroup) :
    ∀ marker, marker ∈ left.toList ↔ marker ∈ right.toList := by
  intro marker
  have equal := valid (probe marker)
  change eval 1 (probe marker) left = eval 1 (probe marker) right at equal
  have absent : (marker ∉ left.toList) ↔ (marker ∉ right.toList) := by
    rw [← all_probe_low_iff marker left.toList, ← all_probe_low_iff marker right.toList,
      ← eval_low_iff 1 (probe marker) left, ← eval_low_iff 1 (probe marker) right, equal]
  constructor
  · intro present
    by_cases other : marker ∈ right.toList
    · exact other
    · exact False.elim ((absent.mpr other) present)
  · intro present
    by_cases other : marker ∈ left.toList
    · exact other
    · exact False.elim ((absent.mp other) present)

theorem four_of_observations (valuation : α → Fin 6) (left right : Word α)
    (support : ∀ x, x ∈ left.toList ↔ x ∈ right.toList)
    (initial : ∀ x, UniqueInitial left x ↔ UniqueInitial right x)
    (four : eval 1 valuation left = 4) : eval 1 valuation right = 4 := by
  have leftAbsent := head_absence_of_eval_four 1 (by decide) valuation left four
  rcases (eval_four_left 1 (by decide) valuation left).mp four with ⟨headFour, tailLow⟩
  rcases (initial left.head).mp ⟨rfl, leftAbsent⟩ with ⟨rightHead, rightAbsent⟩
  apply (eval_four_left 1 (by decide) valuation right).mpr
  refine ⟨?_, ?_⟩
  · rw [rightHead]
    exact headFour
  · intro x present
    have inRight : x ∈ right.toList := List.mem_cons_of_mem _ present
    have inLeft := (support x).mpr inRight
    change x ∈ left.head :: left.tail at inLeft
    rcases List.mem_cons.mp inLeft with same | inside
    · exact False.elim (rightAbsent (same ▸ present))
    · exact tailLow x inside

theorem four_iff_of_observations (valuation : α → Fin 6) (left right : Word α)
    (support : ∀ x, x ∈ left.toList ↔ x ∈ right.toList)
    (initial : ∀ x, UniqueInitial left x ↔ UniqueInitial right x) :
    eval 1 valuation left = 4 ↔ eval 1 valuation right = 4 :=
  ⟨four_of_observations valuation left right support initial,
   four_of_observations valuation right left (fun x => (support x).symm)
     (fun x => (initial x).symm)⟩

def SameCutKey (left : List α) (a : α) (right : List α) (b : α) : Prop :=
  depth left = depth right ∧ a = b ∧
  (∀ x, x ∈ left ++ [a] ↔ x ∈ right ++ [b]) ∧
  ∀ x, UniqueInitial (snoc left a) x ↔ UniqueInitial (snoc right b) x

theorem key_of_valid [DecidableEq α] (left right : List α) (a b : α)
    (valid : (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 1).semigroup) :
    SameCutKey left a right b := by
  have degree := valid (fun _ => (2 : Fin 6))
  change eval 1 (fun _ => (2 : Fin 6)) (snoc left a) =
    eval 1 (fun _ => (2 : Fin 6)) (snoc right b) at degree
  rw [eval_all_two, eval_all_two] at degree
  have finalEqual := valid (marker5 a)
  change eval 1 (marker5 a) (snoc left a) = eval 1 (marker5 a) (snoc right b) at finalEqual
  have five := (marker5_final left a a).mpr rfl
  rw [five] at finalEqual
  refine ⟨depthValue_injective degree, ((marker5_final right b a).mp finalEqual.symm).symm, ?_, ?_⟩
  · simpa only [toList_snoc] using support_of_valid (snoc left a) (snoc right b) valid
  · exact initial_marker_of_valid 1 (by decide) _ valid

theorem valid_of_key (left right : List α) (a b : α) (key : SameCutKey left a right b) :
    (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 1).semigroup := by
  rcases key with ⟨degree, finalSame, support, initial⟩
  subst b
  intro valuation
  change eval 1 valuation (snoc left a) = eval 1 valuation (snoc right a)
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
                  · exact eval_long_range valuation _ (snoc_long c d rest a)
                  · exact eval_long_range valuation _ (snoc_long e f tail a)
                  · rw [eval_zero_long valuation _ (snoc_long c d rest a),
                      eval_zero_long valuation _ (snoc_long e f tail a)]
                    exact ⟨fun h x hx => h x ((content x).mpr hx),
                      fun h x hx => h x ((content x).mp hx)⟩
                  · exact four_iff_of_observations valuation _ _ content initial
                  · rw [eval_five, eval_five]

theorem cut_semantic_key_iff (left right : List α) (a b : α) :
    (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 1).semigroup ↔
      SameCutKey left a right b := by
  classical
  exact ⟨key_of_valid left right a b, valid_of_key left right a b⟩

def SameKey (left right : Word α) : Prop :=
  ∃ leftStem a rightStem b, left = snoc leftStem a ∧ right = snoc rightStem b ∧
    SameCutKey leftStem a rightStem b

theorem semantic_key_iff (left right : Word α) :
    (Identity.mk left right).SatisfiedBy (table 1).semigroup ↔ SameKey left right := by
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

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9642SemanticKey

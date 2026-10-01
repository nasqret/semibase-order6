import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations

/-! A complete semantic identity criterion for the literal S9662 table.
The total snoc representation separates capped length, final letter and
the support before the final letter. No derivational reach is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638CommonIdeal
open SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638FourObservations

def snoc : List α → α → Word α
  | [], last => Word.singleton last
  | a :: rest, last => ⟨a, rest ++ [last]⟩

theorem toList_snoc (stem : List α) (last : α) :
    (snoc stem last).toList = stem ++ [last] := by
  cases stem <;> rfl

theorem snoc_exists (word : Word α) : ∃ stem last, word = snoc stem last := by
  rcases word with ⟨head, tail⟩
  induction tail generalizing head with
  | nil => exact ⟨[], head, rfl⟩
  | cons b rest ih =>
      rcases ih b with ⟨stem, last, same⟩
      refine ⟨head :: stem, last, ?_⟩
      apply Word.toList_injective
      have lists := congrArg Word.toList same
      rw [toList_snoc] at lists
      change b :: rest = stem ++ [last] at lists
      change head :: b :: rest = head :: (stem ++ [last])
      exact congrArg (fun xs => head :: xs) lists

theorem snoc_long (a b : α) (rest : List α) (last : α) :
    3 ≤ (snoc (a :: b :: rest) last).toList.length := by
  simp [toList_snoc, Nat.add_comm, Nat.add_left_comm]

theorem mul_low_upper : ∀ (a b : Fin 6), Low a → ¬ Low b → mul 3 a b = b := by
  unfold Low
  decide

theorem mul_upper : ∀ (a b : Fin 6), ¬ Low a →
    mul 3 a b = if b = 3 ∨ b = 4 then 3 else 5 := by
  unfold Low
  decide

theorem mul_zero_five : ∀ (a : Fin 6), mul 3 a 0 = 5 ↔ ¬ Low a := by
  unfold Low
  decide

theorem mul_three : ∀ (a : Fin 6), mul 3 a 3 = 3 := by decide

theorem mul_zero_not_three : ∀ (a : Fin 6), mul 3 a 0 ≠ 3 := by decide

def allLow (valuation : α → Fin 6) (letters : List α) : Bool :=
  letters.all fun a => decide ((valuation a).val < 3)

theorem allLow_eq_true (valuation : α → Fin 6) (letters : List α) :
    allLow valuation letters = true ↔ ∀ a ∈ letters, Low (valuation a) := by
  simp [allLow, List.all_eq_true, Low]

def longValue (flag : Bool) (last : Fin 6) : Fin 6 :=
  if flag = true then (if last.val < 3 then 0 else last)
  else if last = 3 ∨ last = 4 then 3 else 5

theorem eval_long (valuation : α → Fin 6) (a b : α) (rest : List α) (last : α) :
    eval 3 valuation (snoc (a :: b :: rest) last) =
      longValue (allLow valuation (a :: b :: rest)) (valuation last) := by
  classical
  let stemWord : Word α := ⟨a, b :: rest⟩
  have cut : snoc (a :: b :: rest) last = stemWord ++ Word.singleton last := rfl
  by_cases low : ∀ x ∈ a :: b :: rest, Low (valuation x)
  · have flag := (allLow_eq_true valuation (a :: b :: rest)).mpr low
    rw [longValue, flag, if_pos rfl]
    by_cases lastLow : Low (valuation last)
    · have lastSmall : (valuation last).val < 3 := lastLow
      rw [if_pos lastSmall]
      apply eval_zero_of_low_long
      · intro x present
        rw [toList_snoc] at present
        rcases List.mem_append.mp present with before | final
        · exact low x before
        · have same : x = last := by simpa using final
          subst x
          exact lastLow
      · exact snoc_long a b rest last
    · have lastNotSmall : ¬ (valuation last).val < 3 := lastLow
      rw [if_neg lastNotSmall, cut, eval_snoc]
      exact mul_low_upper _ _ ((eval_low_iff 3 valuation stemWord).mpr low) lastLow
  · have flag : allLow valuation (a :: b :: rest) = false := by
      cases value : allLow valuation (a :: b :: rest) with
      | false => rfl
      | true => exact False.elim (low ((allLow_eq_true valuation _).mp value))
    rw [longValue, flag, if_neg (by decide), cut, eval_snoc]
    apply mul_upper
    intro isLow
    exact low ((eval_low_iff 3 valuation stemWord).mp isLow)

theorem allLow_congr (valuation : α → Fin 6) (left right : List α)
    (support : ∀ a, a ∈ left ↔ a ∈ right) :
    allLow valuation left = allLow valuation right := by
  cases hl : allLow valuation left <;> cases hr : allLow valuation right
  · rfl
  · have rightLow := (allLow_eq_true valuation right).mp hr
    have leftLow := (allLow_eq_true valuation left).mpr
      (fun a ha => rightLow a ((support a).mp ha))
    rw [hl] at leftLow
    contradiction
  · have leftLow := (allLow_eq_true valuation left).mp hl
    have rightLow := (allLow_eq_true valuation right).mpr
      (fun a ha => leftLow a ((support a).mpr ha))
    rw [hr] at rightLow
    contradiction
  · rfl

def marker3 [DecidableEq α] (marker a : α) : Fin 6 := if a = marker then 3 else 0

theorem marker3_eq_three [DecidableEq α] (marker a : α) :
    marker3 marker a = 3 ↔ a = marker := by
  by_cases same : a = marker <;> simp [marker3, same]

theorem marker3_low [DecidableEq α] (marker a : α) :
    Low (marker3 marker a) ↔ a ≠ marker := by
  by_cases same : a = marker
  · rw [marker3, if_pos same]
    have impossible : ¬ Low (3 : Fin 6) := by unfold Low; decide
    constructor
    · intro low
      exact False.elim (impossible low)
    · intro different
      exact False.elim (different same)
  · rw [marker3, if_neg same]
    constructor
    · intro _
      exact same
    · intro _
      unfold Low
      decide

theorem marker3_final [DecidableEq α] (stem : List α) (last marker : α) :
    eval 3 (marker3 marker) (snoc stem last) = 3 ↔ last = marker := by
  cases stem with
  | nil => exact marker3_eq_three marker last
  | cons a rest =>
      change eval 3 (marker3 marker) (Word.mk a rest ++ Word.singleton last) = 3 ↔ _
      rw [eval_snoc]
      by_cases same : last = marker
      · simp [marker3, same, mul_three]
      · rw [marker3, if_neg same]
        constructor
        · intro impossible
          exact False.elim (mul_zero_not_three _ impossible)
        · intro equal
          exact False.elim (same equal)

theorem marker3_stem [DecidableEq α] (stem : List α) (last marker : α)
    (different : last ≠ marker) :
    eval 3 (marker3 marker) (snoc stem last) = 5 ↔ marker ∈ stem := by
  cases stem with
  | nil => simp [snoc, eval, Word.singleton, marker3, different]
  | cons a rest =>
      change eval 3 (marker3 marker) (Word.mk a rest ++ Word.singleton last) = 5 ↔ _
      have finalZero : marker3 marker last = 0 := by simp [marker3, different]
      rw [eval_snoc, finalZero, mul_zero_five, eval_not_low_iff]
      simp [marker3_low, Word.toList]

theorem marker4_final_stem [DecidableEq α] (stem : List α) (last : α) :
    eval 3 (probe last) (snoc stem last) = 4 ↔ last ∉ stem := by
  cases stem with
  | nil =>
      change probe last last = 4 ↔ last ∉ ([] : List α)
      rw [probe_eq_four]
      simp
  | cons a rest =>
      change eval 3 (probe last) (Word.mk a rest ++ Word.singleton last) = 4 ↔ _
      simpa [Word.toList] using probe_four_right_cut last (Word.mk a rest) last

def depth : List α → Fin 3
  | [] => 0
  | [_] => 1
  | _ :: _ :: _ => 2

def depthValue (degree : Fin 3) : Fin 6 :=
  if degree = 0 then 2 else if degree = 1 then 1 else 0

theorem depthValue_injective : Function.Injective depthValue := by
  intro a b same
  exact (by decide : ∀ (a b : Fin 3), depthValue a = depthValue b → a = b) a b same

theorem eval_all_two (stem : List α) (last : α) :
    eval 3 (fun _ => (2 : Fin 6)) (snoc stem last) = depthValue (depth stem) := by
  cases stem with
  | nil => rfl
  | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b rest =>
          change eval 3 (fun _ => (2 : Fin 6)) (snoc (a :: b :: rest) last) = 0
          exact eval_zero_of_low_long 3 (fun _ => 2) _
            (fun _ _ => by change (2 : Fin 6).val < 3; decide) (snoc_long a b rest last)

def SameCutKey (left : List α) (a : α) (right : List α) (b : α) : Prop :=
  depth left = depth right ∧ a = b ∧ ∀ x, x ∈ left ↔ x ∈ right

theorem depth_of_valid (left right : List α) (a b : α)
    (valid : (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 3).semigroup) :
    depth left = depth right := by
  have equal := valid (fun _ => (2 : Fin 6))
  change eval 3 (fun _ => (2 : Fin 6)) (snoc left a) =
    eval 3 (fun _ => (2 : Fin 6)) (snoc right b) at equal
  rw [eval_all_two, eval_all_two] at equal
  exact depthValue_injective equal

theorem last_of_valid [DecidableEq α] (left right : List α) (a b : α)
    (valid : (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 3).semigroup) :
    a = b := by
  have equal := valid (marker3 a)
  change eval 3 (marker3 a) (snoc left a) = eval 3 (marker3 a) (snoc right b) at equal
  have three := (marker3_final left a a).mpr rfl
  rw [three] at equal
  exact ((marker3_final right b a).mp equal.symm).symm

theorem support_of_valid [DecidableEq α] (left right : List α) (last : α)
    (valid : (Identity.mk (snoc left last) (snoc right last)).SatisfiedBy (table 3).semigroup) :
    ∀ marker, marker ∈ left ↔ marker ∈ right := by
  intro marker
  by_cases same : marker = last
  · subst marker
    have equal := valid (probe last)
    change eval 3 (probe last) (snoc left last) =
      eval 3 (probe last) (snoc right last) at equal
    have absent : (last ∉ left) ↔ (last ∉ right) := by
      rw [← marker4_final_stem left last, ← marker4_final_stem right last, equal]
    constructor
    · intro present
      by_cases hr : last ∈ right
      · exact hr
      · exact False.elim ((absent.mpr hr) present)
    · intro present
      by_cases hl : last ∈ left
      · exact hl
      · exact False.elim ((absent.mp hl) present)
  · have different : last ≠ marker := Ne.symm same
    have equal := valid (marker3 marker)
    change eval 3 (marker3 marker) (snoc left last) =
      eval 3 (marker3 marker) (snoc right last) at equal
    rw [← marker3_stem left last marker different,
      ← marker3_stem right last marker different, equal]

theorem key_of_valid [DecidableEq α] (left right : List α) (a b : α)
    (valid : (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 3).semigroup) :
    SameCutKey left a right b := by
  have finalSame := last_of_valid left right a b valid
  subst b
  exact ⟨depth_of_valid left right a a valid, rfl, support_of_valid left right a valid⟩

theorem valid_of_key (left right : List α) (a b : α) (key : SameCutKey left a right b) :
    (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 3).semigroup := by
  rcases key with ⟨degree, finalSame, support⟩
  subst b
  intro valuation
  change eval 3 valuation (snoc left a) = eval 3 valuation (snoc right a)
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons c rest =>
          cases rest <;> simp [depth] at degree
  | cons c rest =>
      cases rest with
      | nil =>
          cases right with
          | nil => simp [depth] at degree
          | cons d rest =>
              cases rest with
              | nil =>
                  have same : c = d := by
                    have present := (support c).mp (by simp)
                    simpa using present
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
                  rw [eval_long, eval_long, allLow_congr valuation _ _ support]

theorem cut_semantic_key_iff (left right : List α) (a b : α) :
    (Identity.mk (snoc left a) (snoc right b)).SatisfiedBy (table 3).semigroup ↔
      SameCutKey left a right b := by
  classical
  exact ⟨key_of_valid left right a b, valid_of_key left right a b⟩

def SameKey (left right : Word α) : Prop :=
  ∃ leftStem a rightStem b, left = snoc leftStem a ∧ right = snoc rightStem b ∧
    SameCutKey leftStem a rightStem b

theorem semantic_key_iff (left right : Word α) :
    (Identity.mk left right).SatisfiedBy (table 3).semigroup ↔ SameKey left right := by
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

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S9662SemanticKey

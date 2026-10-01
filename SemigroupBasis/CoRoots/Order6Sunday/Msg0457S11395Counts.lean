import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Suffix
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446TailBudget
import SemigroupBasis.Transfer

/-! Arbitrary-word capped counts, first-occurrence order and predicate-count
aggregation. No target-basis derivational reach is assumed. -/

set_option maxRecDepth 1000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Counts

open SemigroupBasis SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0457S11395Semantics Msg0457S11395Markers Msg0457S11395Parity

abbrev countCap := Msg0446TailBudget.cap 2

def nilCapValue (n : Nat) : Fin 6 := if n = 0 then 2 else if n = 1 then 1 else 0

theorem nilCapValue_step (n : Nat) (hit : Bool) :
    mul (nilCapValue n) (if hit then 1 else 2) =
      nilCapValue (n + if hit then 1 else 0) := by
  cases hit <;> cases n with
  | zero => decide
  | succ n => cases n <;> simp [nilCapValue, mul]

theorem nilCountFold (predicate : α → Bool) (xs : List α) (n : Nat) :
    xs.foldl (fun a x => mul a (if predicate x then 1 else 2)) (nilCapValue n) =
      nilCapValue (n + xs.countP predicate) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.countP_cons]
      rw [nilCapValue_step, ih]
      congr 1
      split <;> omega

theorem nilCountEval (predicate : Nat → Bool) (word : Word Nat) :
    table.semigroup.eval (fun x => if predicate x then (1 : Fin 6) else (2 : Fin 6)) word =
      nilCapValue (word.toList.countP predicate) := by
  rw [eval_eq_evalList]
  simpa [evalList, nilCapValue] using nilCountFold predicate word.toList 0

theorem nilCapValue_injective_min {left right : Nat}
    (equal : nilCapValue left = nilCapValue right) : min left 2 = min right 2 := by
  by_cases l0 : left = 0 <;> by_cases l1 : left = 1 <;>
    by_cases r0 : right = 0 <;> by_cases r1 : right = 1 <;>
      simp_all [nilCapValue] <;> omega

theorem groupValue_injective : Function.Injective groupValue := by
  intro left right equal
  cases left <;> cases right <;> simp_all [groupValue]

theorem parityCountEval (predicate : Nat → Bool) (word : Word Nat) :
    table.semigroup.eval (fun x => if predicate x then (3 : Fin 6) else (2 : Fin 6)) word =
      groupValue (parityBit (word.toList.countP predicate)) := by
  rw [eval_eq_evalList, evalList_units]
  · rw [groupBit_eq_parityBit]
    have equal : (fun x => ((if predicate x then (3 : Fin 6) else 2) == 3)) = predicate := by
      funext x
      cases predicate x <;> decide
    rw [equal]
  · intro x _
    cases predicate x <;> simp

theorem countCap_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) (letter : Nat) :
    countCap (identity.lhs.toList.count letter) = countCap (identity.rhs.toList.count letter) := by
  have nilEqual := valid (fun x => if x == letter then (1 : Fin 6) else (2 : Fin 6))
  rw [nilCountEval, nilCountEval] at nilEqual
  have parityEqual := valid (fun x => if x == letter then (3 : Fin 6) else (2 : Fin 6))
  rw [parityCountEval, parityCountEval] at parityEqual
  exact (Msg0446TailBudget.cap_eq_iff 2 _ _).2
    ⟨nilCapValue_injective_min nilEqual,
      parityBit_injective_mod (groupValue_injective parityEqual)⟩

def lrbValue (a : Fin 3) : Fin 6 := if a = 0 then 4 else if a = 1 then 2 else 5

def lrbEmbedding : Embedding leftRegularBandThree.semigroup table.semigroup where
  toFun := lrbValue
  map_mul := by decide
  injective := by
    intro a b equal
    have checked : ∀ a b : Fin 3, lrbValue a = lrbValue b → a = b := by decide
    exact checked a b equal

theorem firstOrder_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList = firstOccurrenceSequence identity.rhs.toList :=
  S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq identity
    (lrbEmbedding.pullback_identity identity valid)

def countSum (xs : List Nat) (predicate : Nat → Bool) : List Nat → Nat
  | [] => 0
  | x :: support => (if predicate x then xs.count x else 0) + countSum xs predicate support

theorem countSum_cons (support : List Nat) (predicate : Nat → Bool) (x : Nat) (xs : List Nat) :
    countSum (x :: xs) predicate support =
      countSum xs predicate support + if predicate x then support.count x else 0 := by
  induction support with
  | nil => simp [countSum]
  | cons y support ih =>
      simp only [countSum, ih, List.count_cons]
      by_cases equal : x = y
      · subst y
        cases predicate x <;> simp <;> omega
      · have reverse : y ≠ x := Ne.symm equal
        cases predicate x <;> cases predicate y <;> simp [equal, reverse] <;> omega

theorem nodup_count_one (support : List Nat) (nodup : support.Nodup) (x : Nat)
    (member : x ∈ support) : support.count x = 1 := by
  induction support with
  | nil => simp at member
  | cons y support ih =>
      obtain ⟨absent, tailNodup⟩ := List.nodup_cons.mp nodup
      by_cases equal : x = y
      · subst y
        simp [List.count_cons_self, List.count_eq_zero.mpr absent]
      · have tailMember : x ∈ support := by simpa [equal] using member
        simpa [List.count_cons, equal, Ne.symm equal] using ih tailNodup tailMember

theorem countSum_eq_countP (support xs : List Nat) (predicate : Nat → Bool)
    (nodup : support.Nodup) (covers : ∀ x ∈ xs, x ∈ support) :
    countSum xs predicate support = xs.countP predicate := by
  induction xs with
  | nil =>
      induction support <;> simp_all [countSum]
  | cons x xs ih =>
      rw [countSum_cons, ih (fun y member => covers y (List.mem_cons_of_mem x member)),
        nodup_count_one support nodup x (covers x (by simp)), List.countP_cons]

theorem countSum_mod_eq (support left right : List Nat) (predicate : Nat → Bool)
    (same : ∀ x, left.count x % 2 = right.count x % 2) :
    countSum left predicate support % 2 = countSum right predicate support % 2 := by
  induction support with
  | nil => rfl
  | cons x support ih =>
      cases hp : predicate x with
      | false => simpa only [countSum, hp, Bool.false_eq_true, if_false, Nat.zero_add] using ih
      | true =>
          simp only [countSum, hp, if_true]
          calc
            (left.count x + countSum left predicate support) % 2 =
                (left.count x % 2 + countSum left predicate support % 2) % 2 := Nat.add_mod _ _ _
            _ = (right.count x % 2 + countSum right predicate support % 2) % 2 := by rw [same x, ih]
            _ = (right.count x + countSum right predicate support) % 2 := (Nat.add_mod _ _ _).symm

theorem countSum_min_eq (support left right : List Nat) (predicate : Nat → Bool)
    (same : ∀ x, min (left.count x) 2 = min (right.count x) 2) :
    min (countSum left predicate support) 2 = min (countSum right predicate support) 2 := by
  induction support with
  | nil => rfl
  | cons x support ih =>
      have headEqual := same x
      cases hp : predicate x with
      | false => simpa only [countSum, hp, Bool.false_eq_true, if_false, Nat.zero_add] using ih
      | true =>
          simp only [countSum, hp, if_true]
          omega

theorem countP_mod_eq (left right : List Nat) (predicate : Nat → Bool)
    (same : ∀ x, left.count x % 2 = right.count x % 2) :
    left.countP predicate % 2 = right.countP predicate % 2 := by
  let support := firstOccurrenceSequence (left ++ right)
  have nodup : support.Nodup := firstOccurrenceSequence_nodup _
  have lc : ∀ x ∈ left, x ∈ support := fun x member =>
    (mem_firstOccurrenceSequence_iff x _).2 (List.mem_append_left right member)
  have rc : ∀ x ∈ right, x ∈ support := fun x member =>
    (mem_firstOccurrenceSequence_iff x _).2 (List.mem_append_right left member)
  rw [← countSum_eq_countP support left predicate nodup lc,
    ← countSum_eq_countP support right predicate nodup rc]
  exact countSum_mod_eq support left right predicate same

theorem countP_min_eq (left right : List Nat) (predicate : Nat → Bool)
    (same : ∀ x, min (left.count x) 2 = min (right.count x) 2) :
    min (left.countP predicate) 2 = min (right.countP predicate) 2 := by
  let support := firstOccurrenceSequence (left ++ right)
  have nodup : support.Nodup := firstOccurrenceSequence_nodup _
  have lc : ∀ x ∈ left, x ∈ support := fun x member =>
    (mem_firstOccurrenceSequence_iff x _).2 (List.mem_append_left right member)
  have rc : ∀ x ∈ right, x ∈ support := fun x member =>
    (mem_firstOccurrenceSequence_iff x _).2 (List.mem_append_right left member)
  rw [← countSum_eq_countP support left predicate nodup lc,
    ← countSum_eq_countP support right predicate nodup rc]
  exact countSum_min_eq support left right predicate same

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Counts

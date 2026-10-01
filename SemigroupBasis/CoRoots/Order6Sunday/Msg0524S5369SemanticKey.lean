import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369Observations
import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Counts

/-! Complete S5369 semantic criterion. Reuses only generic count aggregation
from the earlier owner; no foreign semantic iff, BasisFor, or reach theorem. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369SemanticKey

open SemigroupBasis SemigroupBasis.Examples
open Msg0524S5369Evaluator Msg0524S5369Observations
open Msg0457S11395Counts (countSum countSum_eq_countP)

theorem countSum_cap_eq (bound : Nat) (support left right : List Nat)
    (predicate : Nat → Bool)
    (same : ∀ x, min (left.count x) bound = min (right.count x) bound) :
    min (countSum left predicate support) bound = min (countSum right predicate support) bound := by
  induction support with
  | nil => rfl
  | cons x support ih =>
      have headEqual := same x
      cases hp : predicate x with
      | false => simpa only [countSum, hp, Bool.false_eq_true, if_false, Nat.zero_add] using ih
      | true =>
          simp only [countSum, hp, if_true]
          omega

theorem countP_cap_eq (bound : Nat) (left right : List Nat) (predicate : Nat → Bool)
    (same : ∀ x, min (left.count x) bound = min (right.count x) bound) :
    min (left.countP predicate) bound = min (right.countP predicate) bound := by
  let support := firstOccurrenceSequence (left ++ right)
  have nodup : support.Nodup := firstOccurrenceSequence_nodup _
  have lc : ∀ x ∈ left, x ∈ support := fun x member =>
    (mem_firstOccurrenceSequence_iff x _).2 (List.mem_append_left right member)
  have rc : ∀ x ∈ right, x ∈ support := fun x member =>
    (mem_firstOccurrenceSequence_iff x _).2 (List.mem_append_right left member)
  rw [← countSum_eq_countP support left predicate nodup lc,
    ← countSum_eq_countP support right predicate nodup rc]
  exact countSum_cap_eq bound support left right predicate same

def extra (valuation : α → Fin 6) (threshold : Nat) (letters : List α) : Nat :=
  letters.countP (fun a => decide ((valuation a).val < threshold))

theorem weight_decomposition : ∀ v : Fin 6, v ≠ 5 →
    weight v = 1 + (if v.val < 4 then 1 else 0) + (if v.val < 3 then 1 else 0) +
      (if v.val < 2 then 1 else 0) + (if v.val < 1 then 1 else 0) := by decide

theorem cost_decomposition (valuation : α → Fin 6) (letters : List α)
    (low : ∀ a ∈ letters, valuation a ≠ 5) :
    cost valuation letters = letters.length + extra valuation 4 letters +
      extra valuation 3 letters + extra valuation 2 letters + extra valuation 1 letters := by
  induction letters with
  | nil => rfl
  | cons a rest ih =>
      have tailLow : ∀ b ∈ rest, valuation b ≠ 5 :=
        fun b member => low b (List.mem_cons_of_mem a member)
      rw [cost, ih tailLow, weight_decomposition _ (low a (by simp))]
      simp only [extra, List.countP_cons, List.length_cons, decide_eq_true_eq]
      omega

theorem cost_cap_eq (valuation : Nat → Fin 6) (left right : List Nat)
    (lowLeft : ∀ a ∈ left, valuation a ≠ 5) (lowRight : ∀ a ∈ right, valuation a ≠ 5)
    (lengths : left.length = right.length)
    (same : ∀ x, min (left.count x) (5-left.length) = min (right.count x) (5-left.length)) :
    min (cost valuation left) 5 = min (cost valuation right) 5 := by
  have h4 := countP_cap_eq (5-left.length) left right
    (fun a => decide ((valuation a).val < 4)) same
  have h3 := countP_cap_eq (5-left.length) left right
    (fun a => decide ((valuation a).val < 3)) same
  have h2 := countP_cap_eq (5-left.length) left right
    (fun a => decide ((valuation a).val < 2)) same
  have h1 := countP_cap_eq (5-left.length) left right
    (fun a => decide ((valuation a).val < 1)) same
  rw [cost_decomposition valuation left lowLeft, cost_decomposition valuation right lowRight]
  simp only [extra]
  omega

theorem support_of_counts (left right : List Nat) (bound : Nat) (positive : 0 < bound)
    (same : ∀ x, min (left.count x) bound = min (right.count x) bound) :
    ∀ x, x ∈ left ↔ x ∈ right := by
  intro x
  have equal := same x
  rw [← List.count_pos_iff, ← List.count_pos_iff]
  omega

theorem eval_zero_of_occurrence (valuation : α → Fin 6) (word : Word α)
    (head : valuation word.head ≠ 5) (marked : ∃ a ∈ word.toList, valuation a = 5) :
    table.semigroup.eval valuation word = (0 : Fin 6) := by
  apply fold_zero_of_marker valuation word.tail (valuation word.head) head
  rcases marked with ⟨a,member,value⟩
  rcases List.mem_cons.mp member with same | tailMember
  · subst a
    exact False.elim (head value)
  · exact ⟨a,tailMember,value⟩

theorem valid_of_key (left right : Word Nat) (key : SameKey left right) :
    (Identity.mk left right).SatisfiedBy table.semigroup := by
  classical
  change ∀ valuation : Nat → Fin 6,
    table.semigroup.eval valuation left = table.semigroup.eval valuation right
  rcases key with ⟨heads,lengths,counts⟩
  by_cases long : 5 ≤ left.toList.length
  · have rightLong : 5 ≤ right.toList.length := by
      unfold lengthCap at lengths
      omega
    intro valuation
    change table.semigroup.eval valuation left = table.semigroup.eval valuation right
    rw [eval_long valuation left long, eval_long valuation right rightLong, heads]
  · have short : left.toList.length < 5 := by omega
    have rightShort : right.toList.length < 5 := by
      unfold lengthCap at lengths
      omega
    have equalLength : left.toList.length = right.toList.length := by
      unfold lengthCap at lengths
      omega
    have sameCounts : ∀ x, min (left.toList.count x) (5-left.toList.length) =
        min (right.toList.count x) (5-left.toList.length) := by
      intro x
      have h := counts x
      unfold lengthCap at h
      omega
    have support := support_of_counts left.toList right.toList (5-left.toList.length)
      (by omega) sameCounts
    intro valuation
    change table.semigroup.eval valuation left = table.semigroup.eval valuation right
    by_cases head : valuation left.head = 5
    · have rightHead : valuation right.head = 5 := by simpa [← heads] using head
      exact ((eval_five_iff valuation left).mpr head).trans
        ((eval_five_iff valuation right).mpr rightHead).symm
    · have rightHead : valuation right.head ≠ 5 := by simpa [← heads] using head
      by_cases marked : ∃ a ∈ left.toList, valuation a = 5
      · have rightMarked : ∃ a ∈ right.toList, valuation a = 5 := by
          rcases marked with ⟨a,member,value⟩
          exact ⟨a,(support a).mp member,value⟩
        rw [eval_zero_of_occurrence valuation left head marked,
          eval_zero_of_occurrence valuation right rightHead rightMarked]
      · have lowLeft : ∀ a ∈ left.toList, valuation a ≠ 5 :=
          fun a member value => marked ⟨a,member,value⟩
        have lowRight : ∀ a ∈ right.toList, valuation a ≠ 5 :=
          fun a member => lowLeft a ((support a).mpr member)
        rw [eval_of_no_marker valuation left lowLeft, eval_of_no_marker valuation right lowRight]
        apply (nilValue_eq_iff _ _).mpr
        exact cost_cap_eq valuation left.toList right.toList lowLeft lowRight equalLength sameCounts

theorem semantic_key_iff (left right : Word Nat) :
    (Identity.mk left right).SatisfiedBy table.semigroup ↔ SameKey left right :=
  ⟨key_of_valid left right, valid_of_key left right⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369SemanticKey

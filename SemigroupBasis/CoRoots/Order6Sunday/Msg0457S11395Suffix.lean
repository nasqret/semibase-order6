import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Parity

/-! Exact postS observation at a globally simple nilpotent marker. Unlike
S6598, it is the suffix, not the prefix, which can kill the nilpotent. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Suffix

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0457S11395Semantics Msg0457S11395Markers

def suffixAfter (separator : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x = separator then xs else suffixAfter separator xs

theorem suffixAfter_split (separator : Nat) (before after : List Nat)
    (absent : separator ∉ before) :
    suffixAfter separator (before ++ separator :: after) = after := by
  induction before with
  | nil => simp [suffixAfter]
  | cons x xs ih =>
      have different : x ≠ separator := fun equal => absent (by simp [equal])
      have tailAbsent : separator ∉ xs := fun member => absent (List.mem_cons_of_mem x member)
      simpa [suffixAfter, different] using ih tailAbsent

def suffixProbe (separator tested x : Nat) : Fin 6 :=
  if x = separator then 1 else if x = tested then 4 else 2

theorem suffixProbe_safe (separator tested x : Nat) (different : x ≠ separator) :
    2 ≤ (suffixProbe separator tested x).val := by
  simp only [suffixProbe, if_neg different]
  split <;> decide

theorem suffixProbe_isLeft (separator tested x : Nat) (different : tested ≠ separator) :
    isLeft (suffixProbe separator tested x) = (x == tested) := by
  by_cases marker : x = separator <;> by_cases selected : x = tested <;>
    simp_all [suffixProbe, isLeft]

theorem suffixProbe_eval (word : Word Nat) (separator tested : Nat)
    (simple : S5_254.GloballySimple word separator) (different : tested ≠ separator) :
    table.semigroup.eval (suffixProbe separator tested) word =
      if tested ∈ suffixAfter separator word.toList then (0 : Fin 6) else (1 : Fin 6) := by
  have present : separator ∈ word.toList := List.count_pos_iff.mp (by rw [simple]; decide)
  obtain ⟨before, after, shape, beforeAbsent⟩ := PrefixCount.split_first separator present
  have afterAbsent : separator ∉ after := by
    intro member
    have positive := List.count_pos_iff.mpr member
    change word.toList.count separator = 1 at simple
    rw [shape, List.count_append, List.count_cons_self] at simple
    omega
  have beforeSafe : ∀ x ∈ before, 2 ≤ (suffixProbe separator tested x).val := by
    intro x member
    exact suffixProbe_safe separator tested x (fun equal => beforeAbsent (equal ▸ member))
  have afterSafe : ∀ x ∈ after, 2 ≤ (suffixProbe separator tested x).val := by
    intro x member
    exact suffixProbe_safe separator tested x (fun equal => afterAbsent (equal ▸ member))
  rw [eval_eq_evalList, shape,
    uniqueNil_split (suffixProbe separator tested) before after separator
      (by simp [suffixProbe]) beforeSafe afterSafe,
    suffixAfter_split separator before after beforeAbsent]
  have predicate : (fun x => isLeft (suffixProbe separator tested x)) = (fun x => x == tested) :=
    funext (fun x => suffixProbe_isLeft separator tested x different)
  rw [predicate]
  by_cases member : tested ∈ after
  · have yes : after.any (fun x => x == tested) = true :=
      List.any_eq_true.mpr ⟨tested, member, by simp⟩
    simp [yes, member]
  · have no : after.any (fun x => x == tested) = false := by
      cases h : after.any (fun x => x == tested) with
      | false => rfl
      | true =>
          obtain ⟨x, present, equal⟩ := List.any_eq_true.mp h
          have same : x = tested := by simpa using equal
          subst x
          exact False.elim (member present)
    simp [no, member]

theorem suffixSupport_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) (separator tested : Nat)
    (leftSimple : S5_254.GloballySimple identity.lhs separator)
    (rightSimple : S5_254.GloballySimple identity.rhs separator) (different : tested ≠ separator) :
    tested ∈ suffixAfter separator identity.lhs.toList ↔
      tested ∈ suffixAfter separator identity.rhs.toList := by
  have evaluated := valid (suffixProbe separator tested)
  rw [suffixProbe_eval identity.lhs separator tested leftSimple different,
    suffixProbe_eval identity.rhs separator tested rightSimple different] at evaluated
  by_cases left : tested ∈ suffixAfter separator identity.lhs.toList <;>
    by_cases right : tested ∈ suffixAfter separator identity.rhs.toList <;> simp_all

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Suffix

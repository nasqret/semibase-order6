import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Markers
import SemigroupBasis.CoRoots.S5_254Canonical
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468PrefixComparison

/-! The first-occurrence parity observation for arbitrary words. This
includes nonsimple markers, the obstruction to importing S6598's swaps. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Parity

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0457S11395Semantics Msg0457S11395Markers

def parityBit (count : Nat) : Bool := decide (count % 2 = 1)

theorem parityBit_step (count : Nat) (flag : Bool) :
    parityBit (count + if flag then 1 else 0) = (parityBit count != flag) := by
  cases flag with
  | false => simp [parityBit]
  | true =>
      have cases : count % 2 = 0 ∨ count % 2 = 1 := by omega
      rcases cases with h | h <;> simp [parityBit, Nat.add_mod, h]

theorem parityBit_injective_mod {left right : Nat} (equal : parityBit left = parityBit right) :
    left % 2 = right % 2 := by
  have l : left % 2 = 0 ∨ left % 2 = 1 := by omega
  have r : right % 2 = 0 ∨ right % 2 = 1 := by omega
  rcases l with h | h <;> rcases r with k | k <;> simp_all [parityBit]

theorem xorFold_eq_parityBit (predicate : α → Bool) (xs : List α) (count : Nat) :
    xs.foldl (fun bit x => bit != predicate x) (parityBit count) =
      parityBit (count + xs.countP predicate) := by
  induction xs generalizing count with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.countP_cons]
      rw [← parityBit_step count (predicate x), ih]
      congr 1
      split <;> omega

theorem groupBit_eq_parityBit (valuation : α → Fin 6) (xs : List α) :
    groupBit valuation xs = parityBit (xs.countP (fun x => valuation x == (3 : Fin 6))) := by
  simpa [groupBit, parityBit] using
    xorFold_eq_parityBit (fun x => valuation x == (3 : Fin 6)) xs 0

theorem leftValue_injective : Function.Injective leftValue := by
  intro left right equal
  cases left <;> cases right <;> simp_all [leftValue]

def prefixProbe (separator tested x : Nat) : Fin 6 :=
  if x = separator then 4 else if x = tested then 3 else 2

theorem prefixProbe_safe (separator tested x : Nat) : 2 ≤ (prefixProbe separator tested x).val := by
  simp only [prefixProbe]
  split <;> (try split) <;> decide

theorem prefixProbe_units (separator tested x : Nat) (different : x ≠ separator) :
    prefixProbe separator tested x = (2 : Fin 6) ∨ prefixProbe separator tested x = (3 : Fin 6) := by
  simp only [prefixProbe, if_neg different]
  split <;> simp

theorem prefixProbe_group (separator tested x : Nat) (different : tested ≠ separator) :
    (prefixProbe separator tested x == (3 : Fin 6)) = (x == tested) := by
  by_cases marker : x = separator
  · subst x
    simp [prefixProbe, Ne.symm different]
  · by_cases selected : x = tested <;> simp [prefixProbe, marker, selected, different]

/-- Probe a marker's FIRST occurrence even when it is globally repeated. -/
theorem prefixProbe_eval (word : Word Nat) (separator tested : Nat)
    (present : separator ∈ word.toList) (different : tested ≠ separator) :
    table.semigroup.eval (prefixProbe separator tested) word =
      leftValue (parityBit ((S5_254.simplePrefixBefore separator word.toList).count tested)) := by
  obtain ⟨before, after, shape, absent⟩ := PrefixCount.split_first separator present
  have units : ∀ x ∈ before,
      prefixProbe separator tested x = (2 : Fin 6) ∨ prefixProbe separator tested x = (3 : Fin 6) := by
    intro x member
    apply prefixProbe_units
    intro equal
    exact absent (equal ▸ member)
  have marker : isLeft (prefixProbe separator tested separator) = true := by
    simp [prefixProbe, isLeft]
  have countEq : before.countP (fun x => prefixProbe separator tested x == (3 : Fin 6)) =
      before.count tested := by
    have pointwise : (fun x => prefixProbe separator tested x == (3 : Fin 6)) =
        (fun x => x == tested) := funext (fun x => prefixProbe_group separator tested x different)
    rw [pointwise]
    rfl
  rw [eval_eq_evalList, shape,
    firstLeft_split (prefixProbe separator tested) before after separator marker units
      (fun x _ => prefixProbe_safe separator tested x),
    groupBit_eq_parityBit, countEq,
    S5_254.simplePrefixBefore_split separator before after absent]
  simp [prefixProbe]

/-- Necessary parity before every first occurrence, not just simple ones. -/
theorem firstPrefixParity_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) (separator tested : Nat)
    (leftPresent : separator ∈ identity.lhs.toList)
    (rightPresent : separator ∈ identity.rhs.toList) (different : tested ≠ separator) :
    (S5_254.simplePrefixBefore separator identity.lhs.toList).count tested % 2 =
      (S5_254.simplePrefixBefore separator identity.rhs.toList).count tested % 2 := by
  have evaluated := valid (prefixProbe separator tested)
  rw [prefixProbe_eval identity.lhs separator tested leftPresent different,
    prefixProbe_eval identity.rhs separator tested rightPresent different] at evaluated
  exact parityBit_injective_mod (leftValue_injective evaluated)

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Parity

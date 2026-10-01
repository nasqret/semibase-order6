import SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Semantics
import SemigroupBasis.CoRoots.S5_254Family
import SemigroupBasis.Transfer
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446TailBudget

/-! M18 is an actual subsemigroup. Erasing the killer in valuations is NOT
a homomorphism; its evaluation theorem is proved separately by induction.
No M18 derivation is imported into the target B25 theory. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Erasure

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Semantics
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang

def embedValue (a : Fin 5) : Fin 6 := ⟨a.val, by omega⟩

def m18Embedding : Embedding S5_254.table.semigroup table.semigroup where
  toFun := embedValue
  map_mul := by decide
  injective := by
    intro a b equal
    have values := congrArg (fun value : Fin 6 => value.val) equal
    exact Fin.ext values

theorem m18Signature_of_valid (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    S5_254.SameM18Signature identity.lhs identity.rhs :=
  S5_254.sameM18Signature_of_valid identity (m18Embedding.pullback_identity identity valid)

abbrev countCap := Msg0446TailBudget.cap 2

theorem cap_eq_of_m18 {left right : Word Nat}
    (same : S5_254.SameM18Signature left right) (letter : Nat) :
    countCap (left.toList.count letter) = countCap (right.toList.count letter) := by
  apply (Msg0446TailBudget.cap_eq_iff 2 _ _).2
  refine ⟨?_, same.totalParity letter⟩
  have zeros : left.toList.count letter = 0 ↔ right.toList.count letter = 0 := by
    constructor
    · intro zero
      apply List.count_eq_zero.mpr
      intro member
      exact (List.count_eq_zero.mp zero) ((same.support letter).mpr member)
    · intro zero
      apply List.count_eq_zero.mpr
      intro member
      exact (List.count_eq_zero.mp zero) ((same.support letter).mp member)
  have ones : left.toList.count letter = 1 ↔ right.toList.count letter = 1 :=
    same.globallySimple letter
  by_cases zero : left.toList.count letter = 0
  · rw [zero, zeros.mp zero]
  · by_cases one : left.toList.count letter = 1
    · rw [one, ones.mp one]
    · have rightNotZero : right.toList.count letter ≠ 0 := fun h => zero (zeros.mpr h)
      have rightNotOne : right.toList.count letter ≠ 1 := fun h => one (ones.mpr h)
      omega

def eraseKill (a : Fin 6) : Fin 5 :=
  if h : a.val < 5 then ⟨a.val, h⟩ else 3

def erasedDecode (s : Summary) : Fin 5 :=
  if s.zeroSeen || (s.nilCount == 2) then 0
  else if s.nilCount = 1 then (if s.nilParity then 2 else 1)
  else if s.groupParity then 4 else 3

def restore (a : Fin 5) (hasKill blockedNil : Bool) : Fin 6 :=
  if blockedNil then 0
  else if (a == 3 || a == 4) && hasKill then 5 else embedValue a

theorem erasedDecode_empty : erasedDecode emptySummary = 3 := rfl

theorem erasedDecode_push (s : Summary) (a : Fin 6) :
    erasedDecode (push s a) = S5_254.table.mul (erasedDecode s) (eraseKill a) := by
  rcases s with ⟨c,z,g,k,b,p⟩
  have checked : ∀ (c : Fin 3) (z g k b p : Bool) (a : Fin 6),
      erasedDecode (push ⟨c,z,g,k,b,p⟩ a) =
        S5_254.table.mul (erasedDecode ⟨c,z,g,k,b,p⟩) (eraseKill a) := by decide +kernel
  exact checked c z g k b p a

theorem decode_eq_restore (s : Summary) :
    decode s = restore (erasedDecode s) s.hasKill s.blockedNil := by
  rcases s with ⟨c,z,g,k,b,p⟩
  have checked : ∀ (c : Fin 3) (z g k b p : Bool),
      decode ⟨c,z,g,k,b,p⟩ = restore (erasedDecode ⟨c,z,g,k,b,p⟩) k b := by decide +kernel
  exact checked c z g k b p

theorem erasedDecode_fold (valuation : α → Fin 6) (xs : List α) (initial : Summary) :
    erasedDecode (xs.foldl (fun s x => push s (valuation x)) initial) =
      xs.foldl (fun a x => S5_254.table.mul a (eraseKill (valuation x))) (erasedDecode initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, erasedDecode_push]

theorem erasedEval_eq_summary (valuation : α → Fin 6) (word : Word α) :
    S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) word =
      erasedDecode (summaryList valuation word.toList) := by
  rw [summaryList, erasedDecode_fold, erasedDecode_empty]
  cases word with
  | mk head tail =>
      simp only [Word.toList, List.foldl_cons]
      have unit : ∀ a : Fin 5, S5_254.table.mul (3 : Fin 5) a = a := by decide
      rw [unit]
      rfl

theorem eval_eq_restore (valuation : α → Fin 6) (word : Word α) :
    table.semigroup.eval valuation word =
      restore (S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) word)
        (word.toList.any (fun x => valuation x == 5))
        (summaryList valuation word.toList).blockedNil := by
  rw [eval_eq_summary, decode_eq_restore, ← erasedEval_eq_summary, summary_hasKill]

theorem erased_zero_decode_zero (s : Summary) (zero : erasedDecode s = 0) : decode s = 0 := by
  rcases s with ⟨c,z,g,k,b,p⟩
  have checked : ∀ (c : Fin 3) (z g k b p : Bool),
      erasedDecode ⟨c,z,g,k,b,p⟩ = 0 → decode ⟨c,z,g,k,b,p⟩ = 0 := by decide +kernel
  exact checked c z g k b p zero

theorem erased_nil_count (s : Summary)
    (nilValue : erasedDecode s = 1 ∨ erasedDecode s = 2) : s.nilCount.val = 1 := by
  rcases s with ⟨c,z,g,k,b,p⟩
  have checked : ∀ (c : Fin 3) (z g k b p : Bool),
      (erasedDecode ⟨c,z,g,k,b,p⟩ = 1 ∨ erasedDecode ⟨c,z,g,k,b,p⟩ = 2) → c.val = 1 := by decide +kernel
  exact checked c z g k b p nilValue

theorem erased_unit_count (s : Summary)
    (unitValue : erasedDecode s = 3 ∨ erasedDecode s = 4) : s.nilCount.val = 0 := by
  rcases s with ⟨c,z,g,k,b,p⟩
  have checked : ∀ (c : Fin 3) (z g k b p : Bool),
      (erasedDecode ⟨c,z,g,k,b,p⟩ = 3 ∨ erasedDecode ⟨c,z,g,k,b,p⟩ = 4) → c.val = 0 := by decide +kernel
  exact checked c z g k b p unitValue

theorem nil_count_eq_one_of_erased (valuation : α → Fin 6) (word : Word α)
    (nilValue : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) word = (1 : Fin 5) ∨
      S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) word = (2 : Fin 5)) :
    word.toList.countP (fun x => isNil (valuation x)) = 1 := by
  simp only [erasedEval_eq_summary] at nilValue
  have count := erased_nil_count _ nilValue
  rw [summary_nilCount] at count
  omega

theorem nil_count_eq_zero_of_erased (valuation : α → Fin 6) (word : Word α)
    (unitValue : S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) word = (3 : Fin 5) ∨
      S5_254.table.semigroup.eval (fun x => eraseKill (valuation x)) word = (4 : Fin 5)) :
    word.toList.countP (fun x => isNil (valuation x)) = 0 := by
  simp only [erasedEval_eq_summary] at unitValue
  have count := erased_unit_count _ unitValue
  rw [summary_nilCount] at count
  omega

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Erasure

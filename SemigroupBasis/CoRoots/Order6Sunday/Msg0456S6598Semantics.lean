import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! Exact E6598 B25 presentation and an unrestricted literal-table evaluator.
The bounded renderer checks are NOT premises of any theorem below.
No derivational completeness, ReachPlan, or BasisFor is asserted. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Semantics

open SemigroupBasis

def law00 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 0, 0]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [0, 1, 1, 0]⟩⟩
def law07 : Identity Nat := ⟨⟨0, [0, 0, 1, 1]⟩, ⟨1, [0, 0, 0, 1]⟩⟩
def law08 : Identity Nat := ⟨⟨0, [0, 0, 1, 2]⟩, ⟨0, [1, 0, 0, 2]⟩⟩
def law09 : Identity Nat := ⟨⟨0, [0, 0, 1, 2]⟩, ⟨0, [1, 2, 0, 0]⟩⟩
def law10 : Identity Nat := ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩
def law11 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩
def law12 : Identity Nat := ⟨⟨0, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩
def law13 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩
def law14 : Identity Nat := ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩
def law15 : Identity Nat := ⟨⟨0, [1, 1, 1, 2]⟩, ⟨0, [1, 2, 1, 1]⟩⟩
def law16 : Identity Nat := ⟨⟨0, [1, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 1]⟩⟩
def law17 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩
def law18 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩
def law19 : Identity Nat := ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1, 0, 0]⟩⟩
def law20 : Identity Nat := ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def law21 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩
def law22 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩
def law23 : Identity Nat := ⟨⟨2, [1, 0, 2, 3, 0]⟩, ⟨2, [1, 2, 0, 3, 0]⟩⟩
def law24 : Identity Nat := ⟨⟨0, [2, 1, 0, 3, 2]⟩, ⟨2, [0, 1, 0, 3, 2]⟩⟩
def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11, law12, law13, law14, law15, law16, law17, law18, law19, law20, law21, law22, law23, law24]
def basisSHA256 : String := "7ba8ff7938973b86a97d20a0de75a7b24ed0b37acc3f2841e9c5e18eba2f221c"

theorem basis_length : basis.length = 25 := rfl

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 3 then b
  else if a = 4 then
    if b = 1 then 2 else if b = 2 then 1
    else if b = 3 then 4 else if b = 4 then 3 else b
  else if b.val < 3 then 0 else a

def table : FiniteTable := ⟨6, mul, by decide⟩

theorem table_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul a b).val)) =
      [[0,0,0,0,0,0], [0,0,0,1,1,1], [0,0,0,2,2,2],
       [0,1,2,3,4,5], [0,2,1,4,3,5], [0,0,0,5,5,5]] := by decide

theorem left_identity : ∀ a : Fin 6, mul 3 a = a := by decide
theorem right_identity : ∀ a : Fin 6, mul a 3 = a := by decide
theorem zero_left : ∀ a : Fin 6, mul 0 a = 0 := by decide
theorem zero_right : ∀ a : Fin 6, mul a 0 = 0 := by decide

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem models : Models table.semigroup basis := by
  have low : Models table.semigroup
      [law00, law01, law02, law03, law04, law05, law06, law07, law19, law20] :=
    FiniteCertificate.checkModels_sound table _ toFinTwo (by decide +kernel)
  have middle : Models table.semigroup
      [law08, law09, law10, law11, law12, law13, law14, law15, law16, law17, law18] :=
    FiniteCertificate.checkModels_sound table _ toFinThree (by decide +kernel)
  have high : Models table.semigroup [law21, law22, law23, law24] :=
    FiniteCertificate.checkModels_sound table _ toFinFour (by decide +kernel)
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst identity
  all_goals first | exact low _ (by decide) | exact middle _ (by decide) | exact high _ (by decide)

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

/-- Count nilpotent occurrences up to two; retain zero, group parity,
the left-killing idempotent, its precedence before a nilpotent, and the
last nilpotent's parity-adjusted value. No valid-state premise is needed. -/
structure Summary where
  nilCount : Fin 3
  zeroSeen : Bool
  groupParity : Bool
  hasKill : Bool
  blockedNil : Bool
  nilParity : Bool

def emptySummary : Summary := ⟨0, false, false, false, false, false⟩

def isNil (a : Fin 6) : Bool := (a == 1) || (a == 2)

def push (s : Summary) (a : Fin 6) : Summary where
  nilCount := if isNil a then (if s.nilCount = 0 then 1 else 2) else s.nilCount
  zeroSeen := s.zeroSeen || (a == 0)
  groupParity := s.groupParity != (a == 4)
  hasKill := s.hasKill || (a == 5)
  blockedNil := s.blockedNil || (s.hasKill && isNil a)
  nilParity := if isNil a then (a == 2) != s.groupParity else s.nilParity

def decode (s : Summary) : Fin 6 :=
  if s.zeroSeen || s.blockedNil || (s.nilCount == 2) then 0
  else if s.nilCount = 1 then (if s.nilParity then 2 else 1)
  else if s.hasKill then 5
  else if s.groupParity then 4 else 3

theorem decode_empty : decode emptySummary = 3 := rfl

/-- Complete finite transition proof: all 96 states and all six letters. -/
theorem decode_push (s : Summary) (a : Fin 6) :
    decode (push s a) = mul (decode s) a := by
  rcases s with ⟨c, z, g, k, b, p⟩
  have checked : ∀ (c : Fin 3) (z g k b p : Bool) (a : Fin 6),
      decode (push ⟨c, z, g, k, b, p⟩ a) = mul (decode ⟨c, z, g, k, b, p⟩) a := by
    decide +kernel
  exact checked c z g k b p a

def summaryList (valuation : α → Fin 6) (xs : List α) : Summary :=
  xs.foldl (fun s x => push s (valuation x)) emptySummary

/-- Genuine induction over arbitrary lists, not a bounded word enumeration. -/
theorem decode_fold (valuation : α → Fin 6) (xs : List α) (initial : Summary) :
    decode (xs.foldl (fun s x => push s (valuation x)) initial) =
      xs.foldl (fun a x => mul a (valuation x)) (decode initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, decode_push]

theorem eval_eq_summary (valuation : α → Fin 6) (word : Word α) :
    table.semigroup.eval valuation word = decode (summaryList valuation word.toList) := by
  rw [summaryList, decode_fold, decode_empty]
  cases word with
  | mk head tail =>
      simp only [Word.toList, List.foldl_cons, left_identity]
      rfl

theorem fold_zeroSeen (valuation : α → Fin 6) (xs : List α) (initial : Summary) :
    (xs.foldl (fun s x => push s (valuation x)) initial).zeroSeen =
      (initial.zeroSeen || xs.any (fun x => valuation x == 0)) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, List.any_cons]
      exact Bool.or_assoc initial.zeroSeen (valuation x == 0) (xs.any (fun y => valuation y == 0))

theorem summary_zeroSeen (valuation : α → Fin 6) (xs : List α) :
    (summaryList valuation xs).zeroSeen = xs.any (fun x => valuation x == 0) := by
  simpa [summaryList, emptySummary] using fold_zeroSeen valuation xs emptySummary

theorem fold_hasKill (valuation : α → Fin 6) (xs : List α) (initial : Summary) :
    (xs.foldl (fun s x => push s (valuation x)) initial).hasKill =
      (initial.hasKill || xs.any (fun x => valuation x == 5)) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, List.any_cons]
      exact Bool.or_assoc initial.hasKill (valuation x == 5) (xs.any (fun y => valuation y == 5))

theorem summary_hasKill (valuation : α → Fin 6) (xs : List α) :
    (summaryList valuation xs).hasKill = xs.any (fun x => valuation x == 5) := by
  simpa [summaryList, emptySummary] using fold_hasKill valuation xs emptySummary

theorem nilCount_push (s : Summary) (a : Fin 6) :
    (push s a).nilCount.val = min 2 (s.nilCount.val + if isNil a then 1 else 0) := by
  rcases s with ⟨c, z, g, k, b, p⟩
  have checked : ∀ (c : Fin 3) (a : Fin 6),
      (push ⟨c, false, false, false, false, false⟩ a).nilCount.val =
        min 2 (c.val + if isNil a then 1 else 0) := by decide
  exact checked c a

theorem fold_nilCount (valuation : α → Fin 6) (xs : List α) (initial : Summary) :
    (xs.foldl (fun s x => push s (valuation x)) initial).nilCount.val =
      min 2 (initial.nilCount.val + xs.countP (fun x => isNil (valuation x))) := by
  induction xs generalizing initial with
  | nil =>
      simp only [List.foldl_nil, List.countP_nil, Nat.add_zero]
      have bound := initial.nilCount.isLt
      omega
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, List.countP_cons]
      rw [nilCount_push]
      split <;> omega

theorem summary_nilCount (valuation : α → Fin 6) (xs : List α) :
    (summaryList valuation xs).nilCount.val =
      min 2 (xs.countP (fun x => isNil (valuation x))) := by
  simpa [summaryList, emptySummary] using fold_nilCount valuation xs emptySummary

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Semantics

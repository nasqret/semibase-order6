import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Opposite

/-! Exact msg0457 S11395 B12 and an unrestricted literal-table evaluator.
The old eight-law basis is superseded. No unrestricted completeness is
assumed and no S6598 swap rule is imported. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Semantics

open SemigroupBasis

def law00 : Identity Nat := ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩
def law01 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩
def law02 : Identity Nat := ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩
def law03 : Identity Nat := ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩
def law04 : Identity Nat := ⟨⟨0, [0, 0, 1, 1]⟩, ⟨0, [1, 0, 0, 1]⟩⟩
def law05 : Identity Nat := ⟨⟨0, [1, 0, 1, 1]⟩, ⟨0, [1, 1, 1, 0]⟩⟩
def law06 : Identity Nat := ⟨⟨0, [1, 2, 0, 1]⟩, ⟨0, [1, 2, 1, 0]⟩⟩
def law07 : Identity Nat := ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩
def law08 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩
def law09 : Identity Nat := ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 2, 0]⟩⟩
def law10 : Identity Nat := ⟨⟨0, [0, 0, 1, 2, 1]⟩, ⟨0, [1, 0, 0, 2, 1]⟩⟩
def law11 : Identity Nat := ⟨⟨0, [1, 0, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 0, 2]⟩⟩
def basis : List (Identity Nat) := [law00, law01, law02, law03, law04, law05, law06, law07, law08, law09, law10, law11]
def basisSHA256 : String := "f189ba856022446b604efa4c617d2e19bbf11f45dc9978c2d8d559a9767011f0"

theorem basis_length : basis.length = 12 := rfl

def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then 0
  else if a = 1 then (if b = 2 ∨ b = 3 then 1 else 0)
  else if a = 2 then b
  else if a = 3 then
    if b = 2 then 3 else if b = 3 then 2 else if b = 4 then 5 else if b = 5 then 4 else b
  else if b = 0 then 0 else if b = 1 then 1 else a

def table : FiniteTable := ⟨6, mul, by decide⟩

theorem table_rows_exact :
    (List.finRange 6).map (fun a => (List.finRange 6).map (fun b => (mul a b).val)) =
      [[0,0,0,0,0,0], [0,0,1,1,0,0], [0,1,2,3,4,5],
       [0,1,3,2,5,4], [0,1,4,4,4,4], [0,1,5,5,5,5]] := by decide

theorem left_identity : ∀ a : Fin 6, mul 2 a = a := by decide
theorem right_identity : ∀ a : Fin 6, mul a 2 = a := by decide
theorem zero_left : ∀ a : Fin 6, mul 0 a = 0 := by decide
theorem zero_right : ∀ a : Fin 6, mul a 0 = 0 := by decide

private def toFinTwo : Nat → Fin 2
  | 0 => 0
  | _ => 1
private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2
private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem models : Models table.semigroup basis := by
  have low : Models table.semigroup [law00,law01,law02,law03,law04,law05] :=
    FiniteCertificate.checkModels_sound table _ toFinTwo (by decide +kernel)
  have middle : Models table.semigroup [law06,law07,law09,law10,law11] :=
    FiniteCertificate.checkModels_sound table _ toFinThree (by decide +kernel)
  have high : Models table.semigroup [law08] :=
    FiniteCertificate.checkModels_sound table _ toFinFour (by decide +kernel)
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst identity
  all_goals first | exact low _ (by decide) | exact middle _ (by decide) | exact high _ (by decide)

theorem oppositeModels : Models table.semigroup.opposite (reversedBasis basis) :=
  models.oppositeReversed

structure Summary where
  nilCount : Fin 3
  zeroSeen : Bool
  groupParity : Bool
  hasLeft : Bool
  blockedNil : Bool
  leftParity : Bool

def emptySummary : Summary := ⟨0, false, false, false, false, false⟩
def isNil (a : Fin 6) : Bool := a == 1
def isLeft (a : Fin 6) : Bool := (a == 4) || (a == 5)

def push (s : Summary) (a : Fin 6) : Summary where
  nilCount := if isNil a then (if s.nilCount = 0 then 1 else 2) else s.nilCount
  zeroSeen := s.zeroSeen || (a == 0)
  groupParity := s.groupParity != (a == 3)
  hasLeft := s.hasLeft || isLeft a
  blockedNil := s.blockedNil || ((s.nilCount != 0) && isLeft a)
  leftParity := if isLeft a && !s.hasLeft then (a == 5) != s.groupParity else s.leftParity

def decode (s : Summary) : Fin 6 :=
  if s.zeroSeen || s.blockedNil || (s.nilCount == 2) then 0
  else if s.nilCount = 1 then 1
  else if s.hasLeft then (if s.leftParity then 5 else 4)
  else if s.groupParity then 3 else 2

theorem decode_empty : decode emptySummary = 2 := rfl

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

theorem fold_hasLeft (valuation : α → Fin 6) (xs : List α) (initial : Summary) :
    (xs.foldl (fun s x => push s (valuation x)) initial).hasLeft =
      (initial.hasLeft || xs.any (fun x => isLeft (valuation x))) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, List.any_cons]
      exact Bool.or_assoc initial.hasLeft (isLeft (valuation x)) (xs.any (fun y => isLeft (valuation y)))

theorem summary_hasLeft (valuation : α → Fin 6) (xs : List α) :
    (summaryList valuation xs).hasLeft = xs.any (fun x => isLeft (valuation x)) := by
  simpa [summaryList, emptySummary] using fold_hasLeft valuation xs emptySummary

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

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Semantics

import SemigroupBasis.Word

/-! Shared basis-independent evaluator layer for 9638/9642/9643/9662.
The four literal tables share a nilpotent low part and an upper ideal.
No common identity theory, semantic key completeness, or BasisFor is assumed. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638CommonIdeal

open SemigroupBasis

private def row (v0 v1 v2 v3 v4 v5 : Fin 6) (b : Fin 6) : Fin 6 :=
  if b = 0 then v0 else if b = 1 then v1 else if b = 2 then v2
  else if b = 3 then v3 else if b = 4 then v4 else v5

def mul9638 (a b : Fin 6) : Fin 6 :=
  if a = 0 then row 0 0 0 3 3 5 b
  else if a = 1 then row 0 0 0 3 3 5 b
  else if a = 2 then row 0 0 1 3 3 5 b
  else if a = 3 then row 3 3 3 3 3 3 b
  else if a = 4 then row 4 4 4 3 3 3 b
  else row 5 5 5 5 5 5 b

def mul9642 (a b : Fin 6) : Fin 6 :=
  if a = 0 then row 0 0 0 3 3 5 b
  else if a = 1 then row 0 0 0 3 3 5 b
  else if a = 2 then row 0 0 1 3 3 5 b
  else if a = 3 then row 3 3 3 3 3 5 b
  else if a = 4 then row 4 4 4 3 3 5 b
  else row 3 3 3 3 3 5 b

def mul9643 (a b : Fin 6) : Fin 6 :=
  if a = 0 then row 0 0 0 3 3 5 b
  else if a = 1 then row 0 0 0 3 3 5 b
  else if a = 2 then row 0 0 1 3 3 5 b
  else if a = 3 then row 3 3 3 3 3 5 b
  else if a = 4 then row 4 4 4 3 3 5 b
  else row 5 5 5 3 3 5 b

def mul9662 (a b : Fin 6) : Fin 6 :=
  if a = 0 then row 0 0 0 3 4 5 b
  else if a = 1 then row 0 0 0 3 4 5 b
  else if a = 2 then row 0 0 1 3 4 5 b
  else if a = 3 then row 5 5 5 3 3 5 b
  else if a = 4 then row 5 5 5 3 3 5 b
  else row 5 5 5 3 3 5 b

def mul (family : Fin 4) : Fin 6 → Fin 6 → Fin 6 :=
  if family = 0 then mul9638 else if family = 1 then mul9642
  else if family = 2 then mul9643 else mul9662

def Low (value : Fin 6) : Prop := value.val < 3

theorem low_mul : ∀ (family : Fin 4) (a b : Fin 6),
    Low (mul family a b) ↔ Low a ∧ Low b := by
  unfold Low
  decide

theorem zero_low : ∀ (family : Fin 4) (b : Fin 6),
    Low b → mul family 0 b = 0 := by
  unfold Low
  decide

theorem three_low : ∀ (family : Fin 4) (a b c : Fin 6),
    Low a → Low b → Low c → mul family (mul family a b) c = 0 := by
  unfold Low
  decide

theorem fold_low_iff (family : Fin 4) (valuation : α → Fin 6)
    (letters : List α) (initial : Fin 6) :
    Low (letters.foldl (fun state a => mul family state (valuation a)) initial) ↔
      Low initial ∧ ∀ a ∈ letters, Low (valuation a) := by
  induction letters generalizing initial with
  | nil => simp
  | cons a rest ih =>
      simp only [List.foldl_cons, ih, low_mul, List.forall_mem_cons, and_assoc]

theorem fold_zero_of_low (family : Fin 4) (valuation : α → Fin 6)
    (letters : List α) (low : ∀ a ∈ letters, Low (valuation a)) :
    letters.foldl (fun state a => mul family state (valuation a)) 0 = 0 := by
  induction letters with
  | nil => rfl
  | cons a rest ih =>
      rw [List.foldl_cons, zero_low family (valuation a) (low a (by simp))]
      exact ih (fun b hb => low b (by simp [hb]))

def eval (family : Fin 4) (valuation : α → Fin 6) (word : Word α) : Fin 6 :=
  word.tail.foldl (fun state a => mul family state (valuation a)) (valuation word.head)

theorem eval_low_iff (family : Fin 4) (valuation : α → Fin 6) (word : Word α) :
    Low (eval family valuation word) ↔ ∀ a ∈ word.toList, Low (valuation a) := by
  simpa only [eval, Word.toList, List.forall_mem_cons] using
    fold_low_iff family valuation word.tail (valuation word.head)

theorem eval_not_low_iff (family : Fin 4) (valuation : α → Fin 6) (word : Word α) :
    ¬ Low (eval family valuation word) ↔ ∃ a ∈ word.toList, ¬ Low (valuation a) := by
  classical
  rw [eval_low_iff]
  simp

theorem eval_zero_of_low_long (family : Fin 4) (valuation : α → Fin 6) (word : Word α)
    (low : ∀ a ∈ word.toList, Low (valuation a)) (long : 3 ≤ word.toList.length) :
    eval family valuation word = 0 := by
  rcases word with ⟨a, tail⟩
  cases tail with
  | nil => simp [Word.toList] at long
  | cons b tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons c rest =>
          have ha : Low (valuation a) := low a (by simp [Word.toList])
          have hb : Low (valuation b) := low b (by simp [Word.toList])
          have hc : Low (valuation c) := low c (by simp [Word.toList])
          change rest.foldl (fun state d => mul family state (valuation d))
            (mul family (mul family (valuation a) (valuation b)) (valuation c)) = 0
          rw [three_low family (valuation a) (valuation b) (valuation c) ha hb hc]
          exact fold_zero_of_low family valuation rest
            (fun d hd => low d (by simp [Word.toList, hd]))

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Sib9638CommonIdeal

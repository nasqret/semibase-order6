import SemigroupBasis.Generated.S4_71

/-! An actual S4_71 evaluation detects whether a selected letter occurs
after a globally singleton marker. The source table, not a surrogate
scanner or assumed key, supplies every finite multiplication fact. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierProbe

open SemigroupBasis

abbrev blockFactor : Semigroup (Fin 4) := Generated.S4_71.table.semigroup

def probe (selected marker letter : Nat) : Fin 4 :=
  if letter = marker then 1 else if letter = selected then 2 else 3

theorem zero_mul (value : Fin 4) : blockFactor.mul 0 value = 0 := by
  revert value
  decide

theorem identity_mul (value : Fin 4) : blockFactor.mul 3 value = value := by
  revert value
  decide

theorem neutral_mul (a b : Fin 4) (ha : a = 2 ∨ a = 3) (hb : b = 2 ∨ b = 3) :
    blockFactor.mul a b = 2 ∨ blockFactor.mul a b = 3 := by
  revert a b
  decide

theorem neutral_marker (a : Fin 4) (ha : a = 2 ∨ a = 3) : blockFactor.mul a 1 = 1 := by
  revert a
  decide

theorem probe_neutral (selected marker letter : Nat) (different : letter ≠ marker) :
    probe selected marker letter = 2 ∨ probe selected marker letter = 3 := by
  simp only [probe,if_neg different]
  by_cases chosen : letter = selected
  · rw [if_pos chosen]
    exact Or.inl rfl
  · rw [if_neg chosen]
    exact Or.inr rfl

theorem fold_zero (valuation : Nat → Fin 4) (letters : List Nat) :
    letters.foldl (fun state letter => blockFactor.mul state (valuation letter)) 0 = 0 := by
  induction letters with
  | nil => rfl
  | cons head tail ih => rw [List.foldl_cons,zero_mul,ih]

theorem fold_neutral (selected marker : Nat) (letters : List Nat) (initial : Fin 4)
    (neutral : initial = 2 ∨ initial = 3) (absent : marker ∉ letters) :
    letters.foldl (fun state letter => blockFactor.mul state (probe selected marker letter)) initial = 2 ∨
      letters.foldl (fun state letter => blockFactor.mul state (probe selected marker letter)) initial = 3 := by
  induction letters generalizing initial with
  | nil => exact neutral
  | cons head tail ih =>
    have different : head ≠ marker := by
      intro same
      apply absent
      rw [← same]
      exact List.mem_cons_self
    rw [List.foldl_cons]
    exact ih _ (neutral_mul _ _ neutral (probe_neutral selected marker head different))
      (fun member => absent (List.mem_cons_of_mem head member))

theorem suffix_scan (selected marker : Nat) (letters : List Nat)
    (different : selected ≠ marker) (absent : marker ∉ letters) :
    letters.foldl (fun state letter => blockFactor.mul state (probe selected marker letter)) 1 =
      if selected ∈ letters then 0 else 1 := by
  induction letters with
  | nil => simp
  | cons head tail ih =>
    have tailAbsent : marker ∉ tail := fun member => absent (List.mem_cons_of_mem head member)
    have headDifferent : head ≠ marker := by
      intro same
      apply absent
      rw [← same]
      exact List.mem_cons_self
    by_cases selectedHead : head = selected
    · subst head
      have value : probe selected marker selected = 2 := by simp [probe,different]
      rw [List.foldl_cons,value,show blockFactor.mul 1 2 = 0 from rfl,fold_zero]
      simp
    · have value : probe selected marker head = 3 := by simp [probe,headDifferent,selectedHead]
      rw [List.foldl_cons,value,show blockFactor.mul 1 3 = 1 from rfl,ih tailAbsent]
      simp [Ne.symm selectedHead]

theorem eval_as_fold (valuation : Nat → Fin 4) (word : Word Nat) :
    blockFactor.eval valuation word =
      word.toList.foldl (fun state letter => blockFactor.mul state (valuation letter)) 3 := by
  cases word with
  | mk head tail =>
    change tail.foldl (fun state letter => blockFactor.mul state (valuation letter)) (valuation head) =
      tail.foldl (fun state letter => blockFactor.mul state (valuation letter)) (blockFactor.mul 3 (valuation head))
    rw [identity_mul]

theorem eval_singleton_split (word : Word Nat) (front tail : List Nat) (selected marker : Nat)
    (represented : word.toList = front ++ marker :: tail)
    (different : selected ≠ marker) (frontAbsent : marker ∉ front) (tailAbsent : marker ∉ tail) :
    blockFactor.eval (probe selected marker) word = if selected ∈ tail then 0 else 1 := by
  rw [eval_as_fold,represented,List.foldl_append,List.foldl_cons]
  have neutral := fold_neutral selected marker front 3 (Or.inr rfl) frontAbsent
  have value : probe selected marker marker = 1 := by simp [probe]
  rw [value,neutral_marker _ neutral]
  exact suffix_scan selected marker tail different tailAbsent

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierProbe

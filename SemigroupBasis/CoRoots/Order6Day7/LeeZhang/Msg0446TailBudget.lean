import SemigroupBasis.Normalization.StagedNormalization

/-! A closed-form implementation of msg0448's LEAST tail budget for period two.
The stem counts ALL copies already rendered, including first introductions.
These arithmetic results do not assert a class normalizer or its reach proof. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446TailBudget

def cap (threshold count : Nat) : Nat :=
  if count < threshold then count else threshold + (count - threshold) % 2

theorem cap_eq_iff (threshold left right : Nat) :
    cap threshold left = cap threshold right ↔
      min left threshold = min right threshold ∧ left % 2 = right % 2 := by
  by_cases belowLeft : left < threshold <;>
    by_cases belowRight : right < threshold <;>
      simp only [cap, belowLeft, belowRight, if_true, if_false] <;> omega

/-- The least nonnegative addition reaching the requested cap class, when
`stem ≤ count`. The formula depends only on the cap class of count. -/
def tailBudget (threshold stem count : Nat) : Nat :=
  if count < threshold then count - stem
  else (threshold - stem) + (count + stem + (threshold - stem)) % 2

theorem tailBudget_spec (threshold stem count : Nat) (bound : stem ≤ count) :
    cap threshold (stem + tailBudget threshold stem count) = cap threshold count := by
  apply (cap_eq_iff _ _ _).2
  by_cases below : count < threshold
  · simp only [tailBudget, below, if_true]
    omega
  · simp only [tailBudget, below, if_false]
    constructor <;> omega

theorem tailBudget_le_remainder (threshold stem count : Nat) (bound : stem ≤ count) :
    tailBudget threshold stem count ≤ count - stem := by
  by_cases below : count < threshold
  · simp only [tailBudget, below, if_true]
    omega
  · simp only [tailBudget, below, if_false]
    omega

theorem tailBudget_minimal (threshold stem count k : Nat)
    (equal : cap threshold (stem + k) = cap threshold count) :
    tailBudget threshold stem count ≤ k := by
  have components := (cap_eq_iff _ _ _).1 equal
  by_cases below : count < threshold
  · simp only [tailBudget, below, if_true]
    omega
  · simp only [tailBudget, below, if_false]
    omega

theorem tailBudget_eq_of_cap_eq (threshold stem left right : Nat)
    (equal : cap threshold left = cap threshold right) :
    tailBudget threshold stem left = tailBudget threshold stem right := by
  have components := (cap_eq_iff _ _ _).1 equal
  by_cases belowLeft : left < threshold <;>
    by_cases belowRight : right < threshold <;>
      simp only [tailBudget, belowLeft, belowRight, if_true, if_false] <;> omega

theorem tailBudget_characterization (threshold stem count k : Nat) (bound : stem ≤ count) :
    k = tailBudget threshold stem count ↔
      cap threshold (stem + k) = cap threshold count ∧
        ∀ smaller, cap threshold (stem + smaller) = cap threshold count → k ≤ smaller := by
  constructor
  · rintro rfl
    exact ⟨tailBudget_spec _ _ _ bound, fun smaller equal => tailBudget_minimal _ _ _ _ equal⟩
  · rintro ⟨equal, minimal⟩
    exact Nat.le_antisymm (minimal _ (tailBudget_spec _ _ _ bound))
      (tailBudget_minimal _ _ _ _ equal)

/-- A first introduction must be positive, even if the required prefix bit is zero. -/
def firstCopies (bit : Nat) : Nat := if bit = 0 then 2 else 1

theorem firstCopies_positive (bit : Nat) : 0 < firstCopies bit := by
  unfold firstCopies
  split <;> omega

theorem firstCopies_parity (bit : Nat) (binary : bit < 2) : firstCopies bit % 2 = bit := by
  unfold firstCopies
  split <;> omega

theorem firstCopies_minimal (bit count : Nat)
    (positive : 0 < count) (parity : count % 2 = bit) :
    firstCopies bit ≤ count := by
  unfold firstCopies
  split <;> omega

theorem amended_four_flips_five_occurrences :
    tailBudget 3 4 5 = 1 ∧ cap 3 (4 + tailBudget 3 4 5) = cap 3 5 := by decide

theorem first_introduction_even_requires_two :
    firstCopies 0 = 2 ∧ firstCopies 0 % 2 = 0 ∧ (1 : Nat) % 2 ≠ 0 := by decide

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446TailBudget

import SemigroupBasis.CoRoots.Order6SporadicSection18SaturationMeasure

/-! A shared, strictly ordered, duplicate-free alphabet containing exactly the
globally nonsimple letters of an arbitrary word. The numerical range is derived
from the word itself, not imposed as a bound on the theorem. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

def maxLetter : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxLetter xs)

theorem mem_le_maxLetter (letters : List Nat) (x : Nat) : x ∈ letters → x ≤ maxLetter letters := by
  induction letters with
  | nil => intro impossible; cases impossible
  | cons head tail ih =>
      intro member
      rcases List.mem_cons.mp member with equal | member
      · subst x
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

def nonSimpleAlphabet (letters : List Nat) : List Nat :=
  (List.range (maxLetter letters + 1)).filter (fun x => decide (x ∈ letters ∧ letters.count x ≠ 1))

theorem nonSimpleAlphabet_mem (letters : List Nat) (x : Nat) :
    x ∈ nonSimpleAlphabet letters ↔ x ∈ letters ∧ letters.count x ≠ 1 := by
  have filtered : x ∈ nonSimpleAlphabet letters ↔
      x < maxLetter letters + 1 ∧ (x ∈ letters ∧ letters.count x ≠ 1) := by
    simp [nonSimpleAlphabet]
  rw [filtered]
  constructor
  · exact And.right
  · intro member
    exact ⟨Nat.lt_succ_of_le (mem_le_maxLetter letters x member.1), member⟩

theorem nonSimpleAlphabet_ordered (letters : List Nat) :
    (nonSimpleAlphabet letters).Pairwise (· < ·) :=
  List.Pairwise.filter (fun x => decide (x ∈ letters ∧ letters.count x ≠ 1))
    (List.pairwise_lt_range (n := maxLetter letters + 1))

theorem nonSimpleAlphabet_nodup (letters : List Nat) : (nonSimpleAlphabet letters).Nodup :=
  List.nodup_iff_pairwise_ne.mpr ((nonSimpleAlphabet_ordered letters).imp (fun less => Nat.ne_of_lt less))

theorem GoodBlock.ordered {alphabet block : List Nat} (good : GoodBlock alphabet block)
    (alphabetOrdered : alphabet.Pairwise (· < ·)) : block.Pairwise (· < ·) := by
  have filtered : (normalizeBlock alphabet block).Pairwise (· < ·) :=
    List.Pairwise.filter (fun x => decide (x ∈ block)) alphabetOrdered
  rw [good.2] at filtered
  exact filtered

theorem GoodBlock.nodup {alphabet block : List Nat} (good : GoodBlock alphabet block)
    (alphabetOrdered : alphabet.Pairwise (· < ·)) : block.Nodup :=
  List.nodup_iff_pairwise_ne.mpr ((good.ordered alphabetOrdered).imp (fun less => Nat.ne_of_lt less))

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.nonSimpleAlphabet_mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.nonSimpleAlphabet_ordered
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.nonSimpleAlphabet_nodup
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.GoodBlock.ordered
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.GoodBlock.nodup

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

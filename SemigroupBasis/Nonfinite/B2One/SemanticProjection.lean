import SemigroupBasis.Examples.B2OneNonfinite

namespace SemigroupBasis.Nonfinite.B2One

open SemigroupBasis
open SemigroupBasis.Examples.B2One

/-!
Semantic projection lemmas for Sapir's reconstruction of Perkins's proof.

The first indispensable step is deletion soundness for the concrete
`B₂¹` table: a valid identity remains valid after all letters outside a
chosen Boolean projection are evaluated at the identity element.
-/

private def evalList
    (valuation : Nat → Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl
    (fun current letter => mul current (valuation letter)) one

private theorem evalList_toList
    (valuation : Nat → Fin 6) (word : Word Nat) :
    evalList valuation word.toList =
      table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      simp only [evalList, Word.toList, List.foldl_cons, Semigroup.eval]
      rw [one_mul]
      rfl

private def deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6) (letter : Nat) : Fin 6 :=
  if keep letter then valuation letter else one

private theorem foldl_deletionValuation
    (keep : Nat → Bool) (valuation : Nat → Fin 6)
    (letters : List Nat) (initial : Fin 6) :
    letters.foldl
        (fun current letter =>
          mul current (deletionValuation keep valuation letter))
        initial =
      (letters.filter keep).foldl
        (fun current letter => mul current (valuation letter))
        initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.foldl_cons, List.filter_cons]
      by_cases kept : keep letter
      · rw [ih]
        simp [deletionValuation, kept]
      · rw [ih]
        simp [deletionValuation, kept, mul_one]

private theorem filtered_eval_equal
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (keep : Nat → Bool) (valuation : Nat → Fin 6) :
    evalList valuation (left.toList.filter keep) =
      evalList valuation (right.toList.filter keep) := by
  change
    (left.toList.filter keep).foldl
        (fun current letter => mul current (valuation letter)) one =
      (right.toList.filter keep).foldl
        (fun current letter => mul current (valuation letter)) one
  rw [← foldl_deletionValuation keep valuation left.toList one,
    ← foldl_deletionValuation keep valuation right.toList one]
  change
    evalList (deletionValuation keep valuation) left.toList =
      evalList (deletionValuation keep valuation) right.toList
  rw [evalList_toList, evalList_toList]
  exact valid (deletionValuation keep valuation)

/-- Evaluation equality for every Boolean deletion projection of a valid
identity of the concrete Brandt monoid. -/
theorem valid_identity_filtered_eval_equal
    {left right : Word Nat}
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (keep : Nat → Bool) (valuation : Nat → Fin 6) :
    evalList valuation (left.toList.filter keep) =
    evalList valuation (right.toList.filter keep) :=
  filtered_eval_equal valid keep valuation

def pairKeep (first second letter : Nat) : Bool :=
  letter == first || letter == second

private def pairValuation
    (first second : Nat) (valuation : Nat → Fin 6) (letter : Nat) : Fin 6 :=
  if letter = first then valuation 0
  else if letter = second then valuation 1
  else one

private theorem alternating_not_equivalent_nested
    {first second : Nat} (different : first ≠ second) :
    ¬(∀ valuation : Nat → Fin 6,
      evalList valuation [first, second, first, second] =
        evalList valuation [first, second, second, first]) := by
  intro equal
  apply xyxy_not_satisfied
  intro valuation
  have concrete := equal (pairValuation first second valuation)
  simpa [evalList, pairValuation, different, Ne.symm different,
    SemigroupBasis.Nonfinite.B2One.xyxy,
    SemigroupBasis.Nonfinite.B2One.xyyx, Semigroup.eval] using concrete

private theorem alternating_not_equivalent_crossed
    {first second : Nat} (different : first ≠ second) :
    ¬(∀ valuation : Nat → Fin 6,
      evalList valuation [first, second, first, second] =
        evalList valuation [second, first, first, second]) := by
  intro equal
  apply xyxy_yxxy_not_satisfied
  intro valuation
  have concrete := equal (pairValuation first second valuation)
  simpa [evalList, pairValuation, different, Ne.symm different,
    SemigroupBasis.Nonfinite.B2One.xyxy,
    SemigroupBasis.Nonfinite.B2One.yxxy, Semigroup.eval] using concrete

/-- A word in the semantic class of a Perkins left side cannot change the
two-letter nested projection into an alternating projection. This is the
formal use of `xyyx ≈ yxxy` together with the failure of both alternating
four-letter identities in Sapir's proof. -/
theorem semanticClass_forbids_alternating_pair
    {anchor current : Word Nat} {first second : Nat}
    (different : first ≠ second)
    (semantic :
      (Identity.mk anchor current).SatisfiedBy table.semigroup)
    (anchorProjection :
      anchor.toList.filter (pairKeep first second) =
          [first, second, second, first] ∨
        anchor.toList.filter (pairKeep first second) =
          [second, first, first, second])
    (currentProjection :
      current.toList.filter (pairKeep first second) =
          [first, second, first, second] ∨
        current.toList.filter (pairKeep first second) =
          [second, first, second, first]) :
    False := by
  rcases anchorProjection with anchorNested | anchorCrossed
  · rcases currentProjection with currentAlternating | currentReverse
    · apply alternating_not_equivalent_nested different
      intro valuation
      have equal :=
        valid_identity_filtered_eval_equal semantic
          (pairKeep first second) valuation
      simpa [anchorNested, currentAlternating] using equal.symm
    · apply alternating_not_equivalent_crossed
        (first := second) (second := first) (Ne.symm different)
      intro valuation
      have equal :=
        valid_identity_filtered_eval_equal semantic
          (pairKeep first second) valuation
      simpa [anchorNested, currentReverse] using equal.symm
  · rcases currentProjection with currentAlternating | currentReverse
    · apply alternating_not_equivalent_crossed different
      intro valuation
      have equal :=
        valid_identity_filtered_eval_equal semantic
          (pairKeep first second) valuation
      simpa [anchorCrossed, currentAlternating] using equal.symm
    · apply alternating_not_equivalent_nested
        (first := second) (second := first) (Ne.symm different)
      intro valuation
      have equal :=
        valid_identity_filtered_eval_equal semantic
          (pairKeep first second) valuation
      simpa [anchorCrossed, currentReverse] using equal.symm

end SemigroupBasis.Nonfinite.B2One

import SemigroupBasis.CoRoots.Order6SporadicSection25HeadDetection

/-! Restrict actual factor identities by mapping discarded letters to a
proved two-sided unit. List filtering is used only at typed Word boundaries. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

def unitMask {S : Type} (keep : Nat → Bool) (one : S) (valuation : Nat → S) : Nat → S :=
  fun letter => if keep letter then valuation letter else one

theorem foldl_unitMask_filter {S : Type} (G : Semigroup S) (one : S)
    (rightUnit : ∀ value, G.mul value one = value)
    (keep : Nat → Bool) (valuation : Nat → S) (letters : List Nat) (initial : S) :
    letters.foldl (fun value letter => G.mul value (unitMask keep one valuation letter)) initial =
      (letters.filter keep).foldl (fun value letter => G.mul value (valuation letter)) initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons letter rest ih =>
      cases kept : keep letter with
      | false => simpa [unitMask, kept, rightUnit] using ih initial
      | true => simpa [unitMask, kept] using ih (G.mul initial (valuation letter))

theorem word_eval_from_unit {S : Type} (G : Semigroup S) (one : S)
    (leftUnit : ∀ value, G.mul one value = value)
    (valuation : Nat → S) (word : Word Nat) :
    G.eval valuation word =
      word.toList.foldl (fun value letter => G.mul value (valuation letter)) one := by
  change word.tail.foldl (fun value letter => G.mul value (valuation letter)) (valuation word.head) =
    word.tail.foldl (fun value letter => G.mul value (valuation letter)) (G.mul one (valuation word.head))
  rw [leftUnit]

theorem valid_restrict_filter {S : Type} (G : Semigroup S) (one : S)
    (leftUnit : ∀ value, G.mul one value = value)
    (rightUnit : ∀ value, G.mul value one = value)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G)
    (keep : Nat → Bool) (left right : Word Nat)
    (leftFilter : identity.lhs.toList.filter keep = left.toList)
    (rightFilter : identity.rhs.toList.filter keep = right.toList) :
    (⟨left,right⟩ : Identity Nat).SatisfiedBy G := by
  intro valuation
  change G.eval valuation left = G.eval valuation right
  have equal := valid (unitMask keep one valuation)
  rw [word_eval_from_unit G one leftUnit, word_eval_from_unit G one leftUnit,
    foldl_unitMask_filter G one rightUnit, foldl_unitMask_filter G one rightUnit,
    leftFilter, rightFilter] at equal
  rw [word_eval_from_unit G one leftUnit, word_eval_from_unit G one leftUnit]
  exact equal

theorem actualAffine_unit_left (value : Fin 4) :
    Generated.Catalogue.S4_96.table.semigroup.opposite.mul (0 : Fin 4) value = value := by
  decide +revert

theorem actualAffine_unit_right (value : Fin 4) :
    Generated.Catalogue.S4_96.table.semigroup.opposite.mul value (0 : Fin 4) = value := by
  decide +revert

theorem actualAffineValid_restrict_filter (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite)
    (keep : Nat → Bool) (left right : Word Nat)
    (leftFilter : identity.lhs.toList.filter keep = left.toList)
    (rightFilter : identity.rhs.toList.filter keep = right.toList) :
    (⟨left,right⟩ : Identity Nat).SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite :=
  valid_restrict_filter Generated.Catalogue.S4_96.table.semigroup.opposite (0 : Fin 4)
    actualAffine_unit_left actualAffine_unit_right identity valid keep left right leftFilter rightFilter

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.foldl_unitMask_filter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.word_eval_from_unit
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.valid_restrict_filter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualAffine_unit_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualAffine_unit_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualAffineValid_restrict_filter

end SemigroupBasis.CoRoots.Order6SporadicSection25

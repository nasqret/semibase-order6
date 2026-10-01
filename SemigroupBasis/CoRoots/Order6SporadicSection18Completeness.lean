import SemigroupBasis.CoRoots.Order6SporadicSection18CanonicalProgress
import SemigroupBasis.CoRoots.Order6SporadicSection18ClosedCanonicalReduction

/-! Unrestricted C7 completeness. The induction consumes one source slot on
every branch. A mismatch is repaired by an actual basis derivation whose output
is canonical, so no permutation-to-derivation or canonical-preservation premise
remains open. The frozen unrestricted reduction supplies the final BasisFor. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

theorem canonical_complete_after_prefix (sourceTail : List Slot) :
    ∀ {left right : Word Nat} {leftAlphabet rightAlphabet : List Nat}
      {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot},
      Actual.SameEval left.toList right.toList →
      CanonicalWitness left.toList leftAlphabet leftFirst leftRest →
      CanonicalWitness right.toList rightAlphabet rightFirst rightRest →
      ∀ (common : List Slot) (current : Slot) (targetTail : List Slot),
        leftFirst :: leftRest = common ++ current :: sourceTail →
        rightFirst :: rightRest = common ++ current :: targetTail →
        ListDerives right.toList left.toList := by
  induction sourceTail with
  | nil =>
      intro left right leftAlphabet rightAlphabet leftFirst rightFirst leftRest rightRest
        same leftWitness rightWitness common current targetTail leftShape rightShape
      have permutation := canonicalResidualPermutation same leftWitness rightWitness common current [] targetTail leftShape rightShape
      have lengths := permutation.length_eq
      have empty : targetTail = [] := List.eq_nil_of_length_eq_zero (by simpa only [List.length_nil] using lengths.symm)
      have equal : right.toList = left.toList := by
        rw [← rightWitness.2.2.2.2.2.2.2.2, ← leftWitness.2.2.2.2.2.2.2.2, rightShape, leftShape, empty]
      rw [equal]
      exact S5_107.ListDerives.refl _
  | cons wanted sourceTail ih =>
      intro left right leftAlphabet rightAlphabet leftFirst rightFirst leftRest rightRest
        same leftWitness rightWitness common current targetTail leftShape rightShape
      have permutation := canonicalResidualPermutation same leftWitness rightWitness common current
        (wanted :: sourceTail) targetTail leftShape rightShape
      have leftNext : leftFirst :: leftRest = (common ++ [current]) ++ wanted :: sourceTail := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using leftShape
      cases targetTail with
      | nil =>
          have lengths := permutation.length_eq
          simp only [List.length_cons, List.length_nil] at lengths
          omega
      | cons other targetTail =>
          by_cases equal : wanted = other
          · subst other
            have rightNext : rightFirst :: rightRest = (common ++ [current]) ++ wanted :: targetTail := by
              simpa only [List.append_assoc, List.cons_append, List.nil_append] using rightShape
            exact ih same leftWitness rightWitness (common ++ [current]) wanted targetTail leftNext rightNext
          · obtain ⟨output, newRest, newTail, step, preserved, outputShape, _, _⟩ :=
              canonical_exchange_step same leftWitness rightWitness common current wanted other
                sourceTail targetTail leftShape rightShape equal
            have semantic := same.trans (Actual.derives_sameEval step)
            have outputNext : rightFirst :: newRest = (common ++ [current]) ++ wanted :: newTail := by
              simpa only [List.append_assoc, List.cons_append, List.nil_append] using outputShape
            exact step.trans (ih semantic leftWitness preserved (common ++ [current]) wanted newTail leftNext outputNext)

private theorem slot_eq_of_parts (left right : Slot)
    (gaps : left.gap = right.gap) (blocks : left.block = right.block) : left = right := by
  cases left
  cases right
  cases gaps
  cases blocks
  rfl

theorem canonical_comparison {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : Actual.SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest) :
    ListDerives left.toList right.toList := by
  have firstEqual := slot_eq_of_parts leftFirst rightFirst
    (leftWitness.2.2.2.2.1.trans rightWitness.2.2.2.2.1.symm)
    (leftWitness.same_first_block rightWitness same)
  have rightShape : rightFirst :: rightRest = [] ++ leftFirst :: rightRest := by
    simp only [List.nil_append, firstEqual]
  exact (canonical_complete_after_prefix leftRest same leftWitness rightWitness [] leftFirst rightRest rfl rightShape).symm

theorem listDerives_toWord (left right : Word Nat) (derivation : ListDerives left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          cases derivation with
          | words proof => exact proof

theorem canonicalForm_complete (identity : Identity Nat)
    (valid : identity.SatisfiedBy Actual.table.semigroup)
    (leftForm : CanonicalForm identity.lhs.toList) (rightForm : CanonicalForm identity.rhs.toList) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨leftAlphabet, leftFirst, leftRest, leftWitness⟩ :
      ∃ alphabet first rest, CanonicalWitness identity.lhs.toList alphabet first rest := leftForm
  obtain ⟨rightAlphabet, rightFirst, rightRest, rightWitness⟩ :
      ∃ alphabet first rest, CanonicalWitness identity.rhs.toList alphabet first rest := rightForm
  exact listDerives_toWord identity.lhs identity.rhs
    (canonical_comparison (Actual.sameEval_valid identity valid) leftWitness rightWitness)

/-- Proposition18.1 for the actual C7 table: the exact frozen22-law list is an
unconditional basis. Representative/opposite endpoint transport and independent
carrier evidence are separate campaign steps, not claims made by this theorem. -/
theorem basisFor_actual : BasisFor Actual.table.semigroup basis := by
  apply basisFor_of_closedCanonicalForms
  intro identity valid leftClosed rightClosed
  exact canonicalForm_complete identity valid leftClosed.canonical rightClosed.canonical

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonical_complete_after_prefix
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonical_comparison
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.listDerives_toWord
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonicalForm_complete
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.basisFor_actual

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

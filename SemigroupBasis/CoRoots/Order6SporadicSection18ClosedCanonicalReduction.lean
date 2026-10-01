import SemigroupBasis.CoRoots.Order6SporadicSection18ClosedCanonicalWord
import SemigroupBasis.CoRoots.Order6SporadicSection18ConnectedReduction

/-! The strengthened canonicalization boundary of Lemma18.6. Connectedness
of the canonical result follows from its repeated nonempty outer block, not
from an unproved assertion that arbitrary C7 rewrites preserve connectedness.
The final BasisFor implication keeps canonical comparison as an open premise. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6SporadicSection12

private theorem first_mem_left {first : Nat} {tail left right : List Nat}
    (shape : first :: tail = left ++ right) (leftNonempty : left ≠ []) : first ∈ left := by
  cases left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons head rest =>
      change first :: tail = head :: (rest ++ right) at shape
      cases shape
      exact List.Mem.head _

private theorem last_mem_right {last : Nat} {body left right : List Nat}
    (shape : body ++ [last] = left ++ right) (rightNonempty : right ≠ []) : last ∈ right := by
  have reversed : last :: body.reverse = right.reverse ++ left.reverse := by
    simpa [List.reverse_append] using congrArg List.reverse shape
  have reversedNonempty : right.reverse ≠ [] := by simpa using rightNonempty
  have member := first_mem_left reversed reversedNonempty
  simpa using member

/-- Every nontrivial cut of a word with a repeated nonempty outer block has
a letter on both sides: a cut inside the first block sees its copy on the
right; a later cut sees the final letter in the first block on the left. -/
theorem repeatedBlock_supportConnected (block middle : List Nat) (nonempty : block ≠ []) :
    ConnectedComponentSupportConnected (block ++ middle ++ block) := by
  have reverseNonempty : block.reverse ≠ [] := by simpa using nonempty
  obtain ⟨last, beforeRev, reverseShape⟩ := List.exists_cons_of_ne_nil reverseNonempty
  have lastShape : block = beforeRev.reverse ++ [last] := by
    simpa only [List.reverse_reverse, List.reverse_cons] using
      congrArg List.reverse reverseShape
  have lastMember : last ∈ block := by
    rw [lastShape]
    exact List.mem_append.mpr (Or.inr (List.Mem.head []))
  intro left right shape leftNonempty rightNonempty
  have compared : block ++ (middle ++ block) = left ++ right := by
    simpa only [List.append_assoc] using shape
  rcases List.append_eq_append_iff.mp compared with
    ⟨rest, leftShape, _⟩ | ⟨rest, blockSplit, rightShape⟩
  · have inLeft : last ∈ left := by
      rw [leftShape]
      exact List.mem_append.mpr (Or.inl lastMember)
    have finalShape : (block ++ middle ++ beforeRev.reverse) ++ [last] = left ++ right := by
      simpa only [lastShape, List.append_assoc] using shape
    exact ⟨last, inLeft, last_mem_right finalShape rightNonempty⟩
  · obtain ⟨first, tail, leftCons⟩ := List.exists_cons_of_ne_nil leftNonempty
    have inLeft : first ∈ left := by
      rw [leftCons]
      exact List.Mem.head tail
    have inBlock : first ∈ block := by
      rw [blockSplit]
      exact List.mem_append.mpr (Or.inl inLeft)
    have inRight : first ∈ right := by
      rw [rightShape]
      exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr inBlock)))
    exact ⟨first, inLeft, inRight⟩

theorem ClosedCanonicalForm.connected {word : Word Nat}
    (formed : ClosedCanonicalForm word.toList) : Connected word := by
  obtain ⟨block, middle, blockNonempty, shape⟩ := formed.repeatedOuter
  obtain ⟨head, tail, blockShape⟩ := List.exists_cons_of_ne_nil blockNonempty
  have squareNonempty : squareList block ≠ [] := by
    rw [blockShape, squareList_cons]
    simp
  have supported : ConnectedComponentSupportConnected word.toList := by
    rw [shape]
    exact repeatedBlock_supportConnected (squareList block) middle squareNonempty
  refine ⟨?_, ?_⟩
  · rw [shape, blockShape, squareList_cons]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rintro ⟨left, right, wordShape, disjoint⟩
    have split : word.toList = left.toList ++ right.toList := by
      rw [wordShape, Word.toList_append]
    have leftNonempty : left.toList ≠ [] := by
      cases left
      simp [Word.toList]
    have rightNonempty : right.toList ≠ [] := by
      cases right
      simp [Word.toList]
    obtain ⟨letter, inLeft, inRight⟩ := supported left.toList right.toList split
      leftNonempty rightNonempty
    exact disjoint letter inLeft inRight

/-- Every word in the unrestricted product-reduction domain with a simple
letter derives to a connected canonical word whose first and last blocks
coincide. This is the required canonical conclusion of Lemma18.6. -/
theorem lemma18_6 (word : Word Nat) (domain : PairwiseDisjointConnectedProduct word)
    (simple : HasSimple word.toList) :
    ∃ normal : Word Nat, Derives basis word normal ∧ Connected normal ∧
      ClosedCanonicalForm normal.toList := by
  obtain ⟨endpoint, interior, _, first⟩ :=
    Connectedization.existsMatchingConnectedDerivative word domain
  have same := Actual.derives_sameEval (S5_107.ListDerives.ofWord first)
  have envelopeSimple : HasSimple (Connectedization.closedEnvelopeWord endpoint interior).toList := by
    obtain ⟨letter, one⟩ := simple
    exact ⟨letter, (same.countOne letter).mp one⟩
  obtain ⟨normal, last, formed⟩ := closedEnvelope_canonical endpoint interior envelopeSimple
  obtain ⟨head, tail, normalShape⟩ := List.exists_cons_of_ne_nil formed.canonical.nonempty
  let target : Word Nat := ⟨head, tail⟩
  have lastList : ListDerives (Connectedization.closedEnvelopeWord endpoint interior).toList
      target.toList := by
    simpa only [target, Word.toList, normalShape] using last
  have lastDerivation : Derives basis
      (Connectedization.closedEnvelopeWord endpoint interior) target :=
    S5_107.ListDerives.toWord lastList
  have targetForm : ClosedCanonicalForm target.toList := by
    simpa only [target, Word.toList, normalShape] using formed
  exact ⟨target, first.trans lastDerivation, targetForm.connected, targetForm⟩

/-- The remaining full C7 obligation is canonical comparison. This theorem
does not supply that premise and is not an unconditional BasisFor certificate. -/
theorem basisFor_of_closedCanonicalForms
    (complete : ∀ identity : Identity Nat,
      identity.SatisfiedBy Actual.table.semigroup →
      ClosedCanonicalForm identity.lhs.toList →
      ClosedCanonicalForm identity.rhs.toList →
      Derives basis identity.lhs identity.rhs) :
    BasisFor Actual.table.semigroup basis := by
  apply Reduction.basisFor_of_simplePairwiseConnected
  intro identity valid leftProduct rightProduct simple
  have original := Actual.sameEval_valid identity valid
  have rightSimple : HasSimple identity.rhs.toList := by
    obtain ⟨letter, one⟩ := simple
    exact ⟨letter, (original.countOne letter).mp one⟩
  obtain ⟨left, leftDerivation, _, leftForm⟩ := lemma18_6 identity.lhs leftProduct simple
  obtain ⟨right, rightDerivation, _, rightForm⟩ := lemma18_6 identity.rhs rightProduct rightSimple
  have normalizedValid : (Identity.mk left right).SatisfiedBy Actual.table.semigroup := by
    intro valuation
    have leftEqual := Derives.sound Actual.models leftDerivation valuation
    have rightEqual := Derives.sound Actual.models rightDerivation valuation
    exact leftEqual.symm.trans ((valid valuation).trans rightEqual)
  have middle := complete ⟨left, right⟩ normalizedValid leftForm rightForm
  exact leftDerivation.trans (middle.trans rightDerivation.symm)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.repeatedBlock_supportConnected
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.ClosedCanonicalForm.connected
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.lemma18_6
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.basisFor_of_closedCanonicalForms

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

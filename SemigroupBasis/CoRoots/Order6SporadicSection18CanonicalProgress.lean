import SemigroupBasis.CoRoots.Order6SporadicSection18PermutationCanonical

/-! The first-mismatch exchange now returns a genuine canonical WORD witness.
The desired prefix grows by one slot and the unprocessed tail strictly shrinks.
Every representation boundary is named, including the output Word.toList. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical
open SemigroupBasis

theorem replace_suffix_keeps_first {first : Slot} {rest : List Slot}
    (common : List Slot) (current : Slot) (oldTail newTail : List Slot)
    (shape : first :: rest = common ++ current :: oldTail) :
    ∃ newRest, common ++ current :: newTail = first :: newRest := by
  cases common with
  | nil =>
      have heads : first = current := (List.cons.inj shape).1
      exact ⟨newTail, by simp only [List.nil_append, heads]⟩
  | cons head tail =>
      have heads : first = head := (List.cons.inj shape).1
      exact ⟨tail ++ current :: newTail, by simp only [List.cons_append, heads]⟩

theorem canonical_exchange_step {left right : Word Nat}
    {leftAlphabet rightAlphabet : List Nat} {leftFirst rightFirst : Slot} {leftRest rightRest : List Slot}
    (same : Actual.SameEval left.toList right.toList)
    (leftWitness : CanonicalWitness left.toList leftAlphabet leftFirst leftRest)
    (rightWitness : CanonicalWitness right.toList rightAlphabet rightFirst rightRest)
    (common : List Slot) (current wanted other : Slot) (sourceTail targetTail : List Slot)
    (leftShape : leftFirst :: leftRest = common ++ current :: wanted :: sourceTail)
    (rightShape : rightFirst :: rightRest = common ++ current :: other :: targetTail)
    (different : wanted ≠ other) :
    ∃ (output : Word Nat) (newRest newTail : List Slot),
      ListDerives right.toList output.toList ∧
      CanonicalWitness output.toList rightAlphabet rightFirst newRest ∧
      rightFirst :: newRest = common ++ current :: wanted :: newTail ∧
      newTail.Perm sourceTail ∧ newTail.length < (wanted :: sourceTail).length := by
  obtain ⟨newTail, step, tailPermutation, _⟩ := canonical_mismatch_derived_prefix same leftWitness rightWitness
    common current wanted other sourceTail targetTail leftShape rightShape different
  obtain ⟨newRest, outputChain⟩ := replace_suffix_keeps_first common current (other :: targetTail)
    (wanted :: newTail) rightShape
  have toSource : (common ++ current :: wanted :: newTail).Perm (leftFirst :: leftRest) := by
    rw [leftShape]
    exact (List.Perm.refl common).append (List.Perm.cons current (tailPermutation.cons wanted))
  have globalPermutation : (rightFirst :: newRest).Perm (rightFirst :: rightRest) := by
    rw [← outputChain]
    exact toSource.trans (canonicalChainPermutation same leftWitness rightWitness)
  have stepToRender : ListDerives right.toList (render (rightFirst :: newRest)) := by
    rw [← outputChain]
    exact step
  have preserved := rightWitness.permuted_of_sameEval newRest (List.Perm.cons_inv globalPermutation)
    (Actual.derives_sameEval stepToRender)
  obtain ⟨head, tail, renderShape, _⟩ := preserved.form.nonsimpleEnds.1
  let output : Word Nat := S5_107.listWordOfCons head tail
  have outputList : output.toList = render (rightFirst :: newRest) := renderShape.symm
  refine ⟨output, newRest, newTail, ?_, ?_, outputChain.symm, tailPermutation, ?_⟩
  · rw [outputList]
    exact stepToRender
  · rw [outputList]
    exact preserved
  · have lengths := tailPermutation.length_eq
    simp only [List.length_cons]
    omega

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.replace_suffix_keeps_first
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical.canonical_exchange_step

end SemigroupBasis.CoRoots.Order6SporadicSection18.Canonical

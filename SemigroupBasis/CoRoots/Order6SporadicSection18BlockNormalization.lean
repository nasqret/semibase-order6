import SemigroupBasis.CoRoots.Order6SporadicSection18Squares

/-! Lemma18.2 and Corollary18.3, with a genuine global nonsimplicity
condition. A block letter may occur only once in the block itself. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18
open SemigroupBasis

/-- Double exactly the selected block, preserving both surrounding contexts. -/
theorem doubleBlock (before block after : List Nat)
    (nonsimple : ∀ x ∈ block, (before ++ block ++ after).count x ≠ 1) :
    ListDerives (before ++ block ++ after) (before ++ squareList block ++ after) := by
  induction block generalizing before with
  | nil => simpa [squareList_nil] using S5_107.ListDerives.refl (basis := basis) (before ++ after)
  | cons x xs ih =>
      have notOne := nonsimple x (by simp)
      have seen : x ∈ before ∨ x ∈ xs ++ after := by
        by_cases prior : x ∈ before
        · exact Or.inl prior
        · by_cases later : x ∈ xs ++ after
          · exact Or.inr later
          · have prefixZero := List.count_eq_zero.mpr prior
            have suffixZero := List.count_eq_zero.mpr later
            have suffixCount : xs.count x + after.count x = 0 := by
              simpa only [List.count_append] using suffixZero
            have exactlyOne : (before ++ (x :: xs) ++ after).count x = 1 := by
              simp only [List.count_append,List.count_cons_self]
              omega
            exact False.elim (notOne exactlyOne)
      have invariant : ∀ y ∈ xs, ((before ++ [x,x]) ++ xs ++ after).count y ≠ 1 := by
        intro y member
        by_cases same : y = x
        · subst y
          simp only [List.count_append,List.count_cons_self,List.count_nil]
          omega
        · simpa [List.count_append,List.count_cons_of_ne (Ne.symm same)] using
            nonsimple y (List.mem_cons_of_mem x member)
      have first : ListDerives (before ++ (x :: xs) ++ after)
          ((before ++ [x,x]) ++ xs ++ after) := by
        simpa [List.append_assoc] using duplicateOccurrence before x (xs ++ after) seen
      have second := ih (before ++ [x,x]) invariant
      simpa [squareList_cons,List.append_assoc] using first.trans second

/-- Lemma18.2, stronger than a fixed sorted/distinct renderer: any finite list
with exactly the block's support may supply its square factors. -/
theorem lemma18_2 (before block after letters : List Nat)
    (nonsimple : ∀ x ∈ block, (before ++ block ++ after).count x ≠ 1)
    (same : ∀ x, x ∈ block ↔ x ∈ letters) :
    ListDerives (before ++ block ++ after) (before ++ squareList letters ++ after) := by
  exact (doubleBlock before block after nonsimple).trans
    ((squareBlocks_same_content block letters same).context before after)

/-- The arbitrary permutation in the paper is explicit, not a supplied
normalization oracle or a bounded list of successful examples. -/
theorem lemma18_2_permutation (before block after letters permuted : List Nat)
    (nonsimple : ∀ x ∈ block, (before ++ block ++ after).count x ≠ 1)
    (same : ∀ x, x ∈ block ↔ x ∈ letters)
    (permutation : letters.Perm permuted) :
    ListDerives (before ++ block ++ after) (before ++ squareList permuted ++ after) :=
  (lemma18_2 before block after letters nonsimple same).trans
    ((permuteSquares permutation).context before after)

/-- Corollary18.3: support is complete on words with no simple letters. -/
theorem corollary18_3 (left right : List Nat)
    (leftNonsimple : ∀ x ∈ left, left.count x ≠ 1)
    (rightNonsimple : ∀ x ∈ right, right.count x ≠ 1)
    (same : ∀ x, x ∈ left ↔ x ∈ right) : ListDerives left right := by
  have first : ListDerives left (squareList left) := by
    simpa using doubleBlock [] left [] (by simpa using leftNonsimple)
  have last : ListDerives right (squareList right) := by
    simpa using doubleBlock [] right [] (by simpa using rightNonsimple)
  exact first.trans ((squareBlocks_same_content left right same).trans last.symm)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.doubleBlock
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.lemma18_2
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.lemma18_2_permutation
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.corollary18_3

end SemigroupBasis.CoRoots.Order6SporadicSection18

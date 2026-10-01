import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Cap303CappedPrefix

/-! Unrestricted comparison for the approved Cap303 B3. The final variable
is retained; its penultimate variable is retained exactly when it is unique.
The capped counts are per variable, not a constant word-length bound. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_83
open SemigroupBasis.CoRoots.S5_303

theorem reducedPerm_of_cappedCounts (a b : List Nat) (p t : Nat)
    (endpoints : p = t ∨ (t ∉ a ∧ t ∉ b))
    (capped : ∀ z, min ((a ++ [p, t]).count z) 2 =
      min ((b ++ [p, t]).count z) 2) :
    (reduceStem p t a).Perm (reduceStem p t b) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_reduceStem, count_reduceStem]
  have total := capped z
  by_cases pt : p = t
  · subst t
    by_cases zp : z = p
    · subst z
      simp [allowance]
    · simpa [allowance, zp, Ne.symm zp, List.count_append,
        List.count_cons] using total
  · by_cases zp : z = p
    · subst z
      have allowanceOne : allowance p t p = 1 := by
        unfold allowance
        rw [if_pos rfl, if_neg pt]
      rw [allowanceOne]
      have totalOne : min (a.count p + 1) 2 = min (b.count p + 1) 2 := by
        simpa [List.count_append, Ne.symm pt] using total
      omega
    · by_cases zt : z = t
      · subst z
        have absent : t ∉ a ∧ t ∉ b := by
          rcases endpoints with equal | absent
          · exact False.elim (pt equal)
          · exact absent
        rw [List.count_eq_zero.mpr absent.1, List.count_eq_zero.mpr absent.2]
      · simpa [allowance, zp, Ne.symm zp, zt, Ne.symm zt,
          List.count_append, List.count_cons] using total

theorem fixedPairComplete (a b : List Nat) (p t : Nat)
    (endpoints : p = t ∨ (t ∉ a ∧ t ∉ b))
    (capped : ∀ z, min ((a ++ [p, t]).count z) 2 =
      min ((b ++ [p, t]).count z) 2) :
    Derives B3 (pairWord a p t) (pairWord b p t) :=
  (normalizeStem a p t).trans
    ((prefixPermutation (reducedPerm_of_cappedCounts a b p t endpoints capped) p t).trans
      (normalizeStem b p t).symm)

/-- Expose two final copies by a permutation of the stem and one rotation.
This stage preserves the full multiplicities, before any capped reduction. -/
theorem makeRepeated (stem : List Nat) (p t : Nat)
    (repeated : t = p ∨ t ∈ stem) :
    ∃ out : List Nat,
      Derives B3 (pairWord stem p t) (pairWord out t t) ∧
      (stem ++ [p, t]).Perm (out ++ [t, t]) := by
  rcases repeated with equal | member
  · subst p
    exact ⟨stem, Derives.refl _, List.Perm.refl _⟩
  · have arrange : stem.Perm (stem.erase t ++ [t]) :=
      (List.perm_cons_erase member).trans (consToEnd t (stem.erase t))
    refine ⟨stem.erase t ++ [p],
      (prefixPermutation arrange p t).trans (rotateAtEnd (stem.erase t) p t), ?_⟩
    rw [List.perm_iff_count]
    intro z
    have counts := (List.perm_iff_count.mp arrange) z
    simp only [List.count_append, List.count_cons, List.count_nil] at counts ⊢
    omega

theorem repeatedPairComplete (a b : List Nat) (p q t : Nat)
    (leftRepeated : t = p ∨ t ∈ a) (rightRepeated : t = q ∨ t ∈ b)
    (capped : ∀ z, min ((a ++ [p, t]).count z) 2 =
      min ((b ++ [q, t]).count z) 2) :
    Derives B3 (pairWord a p t) (pairWord b q t) := by
  obtain ⟨leftStem, leftPath, leftPermutation⟩ := makeRepeated a p t leftRepeated
  obtain ⟨rightStem, rightPath, rightPermutation⟩ := makeRepeated b q t rightRepeated
  have normalizedCaps : ∀ z, min ((leftStem ++ [t, t]).count z) 2 =
      min ((rightStem ++ [t, t]).count z) 2 := by
    intro z
    rw [← (List.perm_iff_count.mp leftPermutation) z,
      ← (List.perm_iff_count.mp rightPermutation) z]
    exact capped z
  exact leftPath.trans
    ((fixedPairComplete leftStem rightStem t t (Or.inl rfl) normalizedCaps).trans
      rightPath.symm)

/-- The screened invariant gives an unrestricted derivation for arbitrary
nonempty words, using only the exact approved three laws. -/
theorem derives_of_capped_endpoint {left right : Word Nat}
    (capped : ∀ z, min (left.toList.count z) 2 = min (right.toList.count z) 2)
    (same : SameContentEndpointSignature left right) : Derives B3 left right := by
  classical
  have leftReconstruct := terminalSplit_renderWord left
  have rightReconstruct := terminalSplit_renderWord right
  cases leftSplitEq : terminalSplit left with
  | singleton leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightFinalProperty : FinalLetter right leftFinal :=
            (same.finalLetter leftFinal).mp (by simp [FinalLetter, leftSplitEq])
          have finals : rightFinal = leftFinal := by
            simpa [FinalLetter, rightSplitEq] using rightFinalProperty
          subst rightFinal
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          exact Derives.refl _
      | pair rightStem rightPenultimate rightFinal =>
          have leftSingleton : IsSingletonWord left := by simp [IsSingletonWord, leftSplitEq]
          have rightSingleton := same.singleton.mp leftSingleton
          simp [IsSingletonWord, rightSplitEq] at rightSingleton
  | pair leftStem leftPenultimate leftFinal =>
      cases rightSplitEq : terminalSplit right with
      | singleton rightFinal =>
          have rightSingleton : IsSingletonWord right := by simp [IsSingletonWord, rightSplitEq]
          have leftSingleton := same.singleton.mpr rightSingleton
          simp [IsSingletonWord, leftSplitEq] at leftSingleton
      | pair rightStem rightPenultimate rightFinal =>
          have rightFinalProperty : FinalLetter right leftFinal :=
            (same.finalLetter leftFinal).mp (by simp [FinalLetter, leftSplitEq])
          have finals : rightFinal = leftFinal := by
            simpa [FinalLetter, rightSplitEq] using rightFinalProperty
          subst rightFinal
          have pairCaps : ∀ z,
              min ((leftStem ++ [leftPenultimate, leftFinal]).count z) 2 =
                min ((rightStem ++ [rightPenultimate, leftFinal]).count z) 2 := by
            intro z
            have total := capped z
            rw [← terminalSplit_renderList left, ← terminalSplit_renderList right,
              leftSplitEq, rightSplitEq] at total
            exact total
          rw [leftSplitEq] at leftReconstruct
          rw [rightSplitEq] at rightReconstruct
          rw [← leftReconstruct, ← rightReconstruct]
          change Derives B3 (pairWord leftStem leftPenultimate leftFinal)
            (pairWord rightStem rightPenultimate leftFinal)
          by_cases leftRepeated : leftFinal = leftPenultimate ∨ leftFinal ∈ leftStem
          · have rightRepeated : leftFinal = rightPenultimate ∨ leftFinal ∈ rightStem := by
              apply Decidable.byContradiction
              intro rightNotRepeated
              have rightParts := not_or.mp rightNotRepeated
              have rightPair : UniqueFinalPair right rightPenultimate leftFinal := by
                simp [UniqueFinalPair, rightSplitEq, rightParts.1, rightParts.2]
              have leftPair := (same.uniqueFinalPair rightPenultimate leftFinal).mpr rightPair
              have leftParts :
                  leftPenultimate = rightPenultimate ∧ leftFinal = leftFinal ∧
                    leftFinal ≠ leftPenultimate ∧ leftFinal ∉ leftStem := by
                simpa [UniqueFinalPair, leftSplitEq] using leftPair
              rcases leftRepeated with equal | member
              · exact leftParts.2.2.1 equal
              · exact leftParts.2.2.2 member
            exact repeatedPairComplete leftStem rightStem leftPenultimate rightPenultimate
              leftFinal leftRepeated rightRepeated pairCaps
          · have leftUniqueParts := not_or.mp leftRepeated
            have leftPair : UniqueFinalPair left leftPenultimate leftFinal := by
              simp [UniqueFinalPair, leftSplitEq, leftUniqueParts.1, leftUniqueParts.2]
            have rightPair := (same.uniqueFinalPair leftPenultimate leftFinal).mp leftPair
            have rightParts :
                rightPenultimate = leftPenultimate ∧ leftFinal = leftFinal ∧
                  leftFinal ≠ rightPenultimate ∧ leftFinal ∉ rightStem := by
              simpa [UniqueFinalPair, rightSplitEq] using rightPair
            have penultimates : rightPenultimate = leftPenultimate := rightParts.1
            subst rightPenultimate
            exact fixedPairComplete leftStem rightStem leftPenultimate leftFinal
              (Or.inr ⟨leftUniqueParts.2, rightParts.2.2.2⟩) pairCaps

theorem basisFor_of_invariants {carrier : Type} (semigroup : Semigroup carrier)
    (models : Models semigroup B3)
    (invariants : ∀ e : Identity Nat, e.SatisfiedBy semigroup →
      (∀ z, min (e.lhs.toList.count z) 2 = min (e.rhs.toList.count z) 2) ∧
        SameContentEndpointSignature e.lhs e.rhs) :
    BasisFor semigroup B3 := by
  refine ⟨models, ?_⟩
  intro e valid
  have observed := invariants e valid
  exact derives_of_capped_endpoint observed.1 observed.2

example : ∀ {left right : Word Nat},
    (∀ z, min (left.toList.count z) 2 = min (right.toList.count z) 2) →
      SameContentEndpointSignature left right → Derives B3 left right :=
  derives_of_capped_endpoint

end SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion

#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.reducedPerm_of_cappedCounts
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.fixedPairComplete
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.makeRepeated
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.repeatedPairComplete
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.derives_of_capped_endpoint
#print axioms SemigroupBasis.CoRoots.Order6Sunday.Cap303Completion.basisFor_of_invariants

import SemigroupBasis.CoRoots.S5_55
import SemigroupBasis.Examples.CyclicFourOne
import SemigroupBasis.Generated.CatalogueOrder5Part01
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_55Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_55

private def finiteFirstSwapLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

private def finiteMultiplicityTransferLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 1]⟩⟩

private def finitePrefixSwapLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨1, [0, 0]⟩⟩

private def finiteSuffixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

private def finitePrefixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

private def finiteLongCollapseLaw : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3]⟩, ⟨0, [0, 0, 0]⟩⟩

private theorem finiteFirstSwapLaw_map :
    finiteFirstSwapLaw.map Fin.val = firstSwapLaw := rfl

private theorem finiteMultiplicityTransferLaw_map :
    finiteMultiplicityTransferLaw.map Fin.val =
      multiplicityTransferLaw := rfl

private theorem finitePrefixSwapLaw_map :
    finitePrefixSwapLaw.map Fin.val = prefixSwapLaw := rfl

private theorem finiteSuffixCommutationLaw_map :
    finiteSuffixCommutationLaw.map Fin.val =
      suffixCommutationLaw := rfl

private theorem finitePrefixCommutationLaw_map :
    finitePrefixCommutationLaw.map Fin.val =
      prefixCommutationLaw := rfl

private theorem finiteLongCollapseLaw_map :
    finiteLongCollapseLaw.map Fin.val = longCollapseLaw := rfl

private theorem models_of_checks
    (T : FiniteTable)
    (firstSwap : T.checkIdentity finiteFirstSwapLaw = true)
    (multiplicityTransfer :
      T.checkIdentity finiteMultiplicityTransferLaw = true)
    (prefixSwap : T.checkIdentity finitePrefixSwapLaw = true)
    (suffixCommutation :
      T.checkIdentity finiteSuffixCommutationLaw = true)
    (prefixCommutation :
      T.checkIdentity finitePrefixCommutationLaw = true)
    (longCollapse :
      T.checkIdentity finiteLongCollapseLaw = true) :
    Models T.semigroup basis := by
  intro e member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← finiteFirstSwapLaw_map]
    exact T.checkIdentityNat_sound finiteFirstSwapLaw firstSwap
  · rw [← finiteMultiplicityTransferLaw_map]
    exact T.checkIdentityNat_sound
      finiteMultiplicityTransferLaw multiplicityTransfer
  · rw [← finitePrefixSwapLaw_map]
    exact T.checkIdentityNat_sound finitePrefixSwapLaw prefixSwap
  · rw [← finiteSuffixCommutationLaw_map]
    exact T.checkIdentityNat_sound
      finiteSuffixCommutationLaw suffixCommutation
  · rw [← finitePrefixCommutationLaw_map]
    exact T.checkIdentityNat_sound
      finitePrefixCommutationLaw prefixCommutation
  · rw [← finiteLongCollapseLaw_map]
    exact T.checkIdentityNat_sound finiteLongCollapseLaw longCollapse

/-- The state of the power `gⁿ` in the embedded `C₄,₁` factor. -/
private def cyclicState (n : Nat) : Fin 4 :=
  if n = 1 then 3
  else if n = 2 then 1
  else if n = 3 then 2
  else 0

private theorem cyclicMul_state_one
    (n : Nat) (nPos : 0 < n) :
    cyclicFourOneMul (cyclicState n) (cyclicState 1) =
      cyclicState (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hn3 : n = 3
      · subst n
        rfl
      · have hn0 : n ≠ 0 := by omega
        have hnext1 : n + 1 ≠ 1 := by omega
        have hnext2 : n + 1 ≠ 2 := by omega
        have hnext3 : n + 1 ≠ 3 := by omega
        apply Fin.ext
        simp [cyclicState, cyclicFourOneMul, hn0, hn1, hn2,
          hn3, hnext1, hnext2, hnext3]

private theorem cyclicMul_state_two
    (n : Nat) (nPos : 0 < n) :
    cyclicFourOneMul (cyclicState n) (cyclicState 2) =
      cyclicState (n + 2) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hn3 : n = 3
      · subst n
        rfl
      · have hn0 : n ≠ 0 := by omega
        have hnext1 : n + 2 ≠ 1 := by omega
        have hnext2 : n + 2 ≠ 2 := by omega
        have hnext3 : n + 2 ≠ 3 := by omega
        apply Fin.ext
        simp [cyclicState, cyclicFourOneMul, hn0, hn1, hn2,
          hn3, hnext1, hnext2, hnext3]

private def weightedValuation (weight : Nat → Nat) : Nat → Fin 4 :=
  fun x => cyclicState (weight x)

private def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => weight x + weightSum weight xs

private theorem cyclicFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current x =>
          cyclicFourOneMul current (weightedValuation weight x))
        (cyclicState acc) =
      cyclicState (acc + weightSum weight xs) := by
  induction xs generalizing acc with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo x with hx | hx
      · rw [show weightedValuation weight x =
          cyclicState 1 by simp [weightedValuation, hx]]
        rw [cyclicMul_state_one acc accPos]
        rw [ih (acc + 1) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega
      · rw [show weightedValuation weight x =
          cyclicState 2 by simp [weightedValuation, hx]]
        rw [cyclicMul_state_two acc accPos]
        rw [ih (acc + 2) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega

private theorem cyclicEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (w : Word Nat) :
    cyclicFourOne.semigroup.eval (weightedValuation weight) w =
      cyclicState (weightSum weight w.toList) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicFourOneMul current (weightedValuation weight x))
            (weightedValuation weight head) =
          cyclicState (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          cyclicState (weight head) by rfl]
      have headPos : 0 < weight head := by
        rcases oneOrTwo head with h | h <;> omega
      rw [cyclicFold_weighted weight oneOrTwo tail
        (weight head) headPos]
      simp [weightSum]

private def unitWeight : Nat → Nat := fun _ => 1

private def doubledWeight (z : Nat) : Nat → Nat :=
  fun x => if x = z then 2 else 1

private theorem weightSum_unit (xs : List Nat) :
    weightSum unitWeight xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [weightSum, unitWeight, ih]
      omega

private theorem weightSum_doubled (z : Nat) (xs : List Nat) :
    weightSum (doubledWeight z) xs = xs.length + xs.count z := by
  induction xs with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      by_cases hx : x = z
      · subst x
        simp [weightSum, doubledWeight, ih]
        omega
      · simp [weightSum, doubledWeight, hx, ih]
        omega

private theorem cyclicEval_unit (w : Word Nat) :
    cyclicFourOne.semigroup.eval (weightedValuation unitWeight) w =
      cyclicState w.toList.length := by
  rw [cyclicEval_weighted unitWeight (by
    intro x
    exact Or.inl rfl)]
  rw [weightSum_unit]

private theorem cyclicEval_doubled (z : Nat) (w : Word Nat) :
    cyclicFourOne.semigroup.eval
        (weightedValuation (doubledWeight z)) w =
      cyclicState (w.toList.length + w.toList.count z) := by
  rw [cyclicEval_weighted (doubledWeight z) (by
    intro x
    by_cases hx : x = z
    · exact Or.inr (by simp [doubledWeight, hx])
    · exact Or.inl (by simp [doubledWeight, hx]))]
  rw [weightSum_doubled]

private theorem cyclicState_eq_one
    {n : Nat} (nPos : 0 < n) :
    cyclicState n = cyclicState 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · exact hn1
    · by_cases hn2 : n = 2
      · subst n
        simp [cyclicState] at h
      · by_cases hn3 : n = 3
        · subst n
          simp [cyclicState] at h
        · simp [cyclicState, hn1, hn2, hn3] at h
  · intro h
    rw [h]

private theorem cyclicState_eq_two
    {n : Nat} (nPos : 0 < n) :
    cyclicState n = cyclicState 2 ↔ n = 2 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · subst n
      simp [cyclicState] at h
    · by_cases hn2 : n = 2
      · exact hn2
      · by_cases hn3 : n = 3
        · subst n
          simp [cyclicState] at h
        · simp [cyclicState, hn1, hn2, hn3] at h
  · intro h
    rw [h]

private theorem cyclicState_eq_three
    {n : Nat} (nPos : 0 < n) :
    cyclicState n = cyclicState 3 ↔ n = 3 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · subst n
      simp [cyclicState] at h
    · by_cases hn2 : n = 2
      · subst n
        simp [cyclicState] at h
      · by_cases hn3 : n = 3
        · exact hn3
        · simp [cyclicState, hn1, hn2, hn3] at h
  · intro h
    rw [h]

private theorem cyclicState_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (h :
      cyclicState (1 + m) =
        cyclicState (1 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 := by omega
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hm with rfl | rfl <;>
    rcases hn with rfl | rfl <;>
    simp [cyclicState] at h ⊢

private theorem cyclicState_two_add_injective
    {m n : Nat} (mLe : m ≤ 2) (nLe : n ≤ 2)
    (h :
      cyclicState (2 + m) =
        cyclicState (2 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hm with rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl <;>
    simp [cyclicState] at h ⊢

private theorem cyclicState_three_add_zero_iff (n : Nat) :
    cyclicState (3 + n) = cyclicState 3 ↔ n = 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hne1 : 3 + n ≠ 1 := by omega
    have hne2 : 3 + n ≠ 2 := by omega
    have hne3 : 3 + n ≠ 3 := by omega
    simp [cyclicState, hne1, hne2, hne3, hn]

private theorem support_of_count_eq
    {u v : Word Nat}
    (counts :
      ∀ z, u.toList.count z = v.toList.count z) :
    SameSupport u v := by
  intro z
  constructor
  · intro member
    have positive : 0 < u.toList.count z :=
      List.count_pos_iff.mpr member
    rw [counts z] at positive
    exact List.count_pos_iff.mp positive
  · intro member
    have positive : 0 < v.toList.count z :=
      List.count_pos_iff.mpr member
    rw [← counts z] at positive
    exact List.count_pos_iff.mp positive

private theorem exact_of_cyclic_separation
    (T : FiniteTable)
    (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    (e : Identity Nat)
    (valid : e.SatisfiedBy T.semigroup)
    (cyclicValid : e.SatisfiedBy cyclicFourOne.semigroup) :
    ExactBasisClass e.lhs e.rhs := by
  have lengthState :
      cyclicState e.lhs.toList.length =
        cyclicState e.rhs.toList.length := by
    have evaluated := cyclicValid (weightedValuation unitWeight)
    rw [cyclicEval_unit, cyclicEval_unit] at evaluated
    exact evaluated
  have weightedState :
      ∀ z,
        cyclicState
            (e.lhs.toList.length + e.lhs.toList.count z) =
          cyclicState
            (e.rhs.toList.length + e.rhs.toList.count z) := by
    intro z
    have evaluated :=
      cyclicValid (weightedValuation (doubledWeight z))
    rw [cyclicEval_doubled, cyclicEval_doubled] at evaluated
    exact evaluated
  have lhsPos : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      apply (cyclicState_eq_one rhsPos).mp
      rw [← lengthState, lhsOne]
    have countEq :
        ∀ z, e.lhs.toList.count z = e.rhs.toList.count z := by
      intro z
      apply cyclicState_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length (a := z) (l := e.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length (a := z) (l := e.rhs.toList))
      · simpa [lhsOne, rhsOne] using weightedState z
    exact Or.inl <|
      lengthOne_eq_of_support e.lhs e.rhs lhsOne rhsOne
        (support_of_count_eq countEq)
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        apply (cyclicState_eq_two rhsPos).mp
        rw [← lengthState, lhsTwo]
      have countEq :
          ∀ z, e.lhs.toList.count z = e.rhs.toList.count z := by
        intro z
        apply cyclicState_two_add_injective
        · simpa [lhsTwo] using
            (List.count_le_length (a := z) (l := e.lhs.toList))
        · simpa [rhsTwo] using
            (List.count_le_length (a := z) (l := e.rhs.toList))
        · simpa [lhsTwo, rhsTwo] using weightedState z
      exact Or.inl <|
        validLengthTwo_eq_of_support_and_order
          T left right orderNe e valid
          (support_of_count_eq countEq) lhsTwo rhsTwo
    · by_cases lhsThree : e.lhs.toList.length = 3
      · have rhsThree : e.rhs.toList.length = 3 := by
          apply (cyclicState_eq_three rhsPos).mp
          rw [← lengthState, lhsThree]
        have countZeroEq :
            ∀ z,
              e.lhs.toList.count z = 0 ↔
                e.rhs.toList.count z = 0 := by
          intro z
          constructor
          · intro lhsZero
            apply (cyclicState_three_add_zero_iff
              (e.rhs.toList.count z)).mp
            simpa [lhsThree, rhsThree, lhsZero] using
              (weightedState z).symm
          · intro rhsZero
            apply (cyclicState_three_add_zero_iff
              (e.lhs.toList.count z)).mp
            simpa [lhsThree, rhsThree, rhsZero] using
              weightedState z
        have support :
            SameSupport e.lhs e.rhs := by
          intro z
          constructor
          · intro lhsMember
            apply Decidable.byContradiction
            intro rhsAbsent
            have rhsZero := List.count_eq_zero.mpr rhsAbsent
            exact
              (List.count_eq_zero.mp
                ((countZeroEq z).mpr rhsZero)) lhsMember
          · intro rhsMember
            apply Decidable.byContradiction
            intro lhsAbsent
            have lhsZero := List.count_eq_zero.mpr lhsAbsent
            exact
              (List.count_eq_zero.mp
                ((countZeroEq z).mp lhsZero)) rhsMember
        exact Or.inr <| Or.inl
          ⟨lhsThree, rhsThree, support⟩
      · have lhsLong : 4 ≤ e.lhs.toList.length := by
          omega
        have rhsNotOne : e.rhs.toList.length ≠ 1 := by
          intro rhsOne
          apply lhsOne
          apply (cyclicState_eq_one lhsPos).mp
          rw [lengthState, rhsOne]
        have rhsNotTwo : e.rhs.toList.length ≠ 2 := by
          intro rhsTwo
          apply lhsTwo
          apply (cyclicState_eq_two lhsPos).mp
          rw [lengthState, rhsTwo]
        have rhsNotThree : e.rhs.toList.length ≠ 3 := by
          intro rhsThree
          apply lhsThree
          apply (cyclicState_eq_three lhsPos).mp
          rw [lengthState, rhsThree]
        have rhsLong : 4 ≤ e.rhs.toList.length := by
          omega
        exact Or.inr <| Or.inr ⟨lhsLong, rhsLong⟩

namespace S5_55

private def cyclicEmbedding :
    Embedding cyclicFourOne.semigroup
      Generated.Catalogue.S5_55.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩
    else if a.val = 1 then ⟨1, by decide⟩
    else if a.val = 2 then ⟨2, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_55.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_55.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

private theorem order_ne :
    Generated.Catalogue.S5_55.mul 3 4 ≠
      Generated.Catalogue.S5_55.mul 4 3 := by
  decide

/-- The exact five-element table separates precisely the shared syntactic
normal-form classes. -/
theorem valid_exactBasisClass
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_55.table.semigroup) :
    ExactBasisClass e.lhs e.rhs :=
  exact_of_cyclic_separation Generated.Catalogue.S5_55.table
    ⟨3, by decide⟩ ⟨4, by decide⟩ order_ne e valid
    (cyclicEmbedding.pullback_identity e valid)

/-- Unconditional representative endpoint for `S5_55`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_55.table.semigroup basis :=
  basis_complete_of_exact Generated.Catalogue.S5_55.table
    models valid_exactBasisClass

/-- Unconditional reverse-word endpoint for the opposite of `S5_55`. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_55.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_55

namespace S5_192

private def cyclicEmbedding :
    Embedding cyclicFourOne.semigroup
      Generated.Catalogue.S5_192.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then ⟨0, by decide⟩
    else if a.val = 1 then ⟨2, by decide⟩
    else if a.val = 2 then ⟨1, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_192.table.semigroup basis :=
  models_of_checks Generated.Catalogue.S5_192.table
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

private theorem order_ne :
    Generated.Catalogue.S5_192.mul 3 4 ≠
      Generated.Catalogue.S5_192.mul 4 3 := by
  decide

/-- The exact five-element table separates precisely the shared syntactic
normal-form classes. -/
theorem valid_exactBasisClass
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy Generated.Catalogue.S5_192.table.semigroup) :
    ExactBasisClass e.lhs e.rhs :=
  exact_of_cyclic_separation Generated.Catalogue.S5_192.table
    ⟨3, by decide⟩ ⟨4, by decide⟩ order_ne e valid
    (cyclicEmbedding.pullback_identity e valid)

/-- Unconditional representative endpoint for `S5_192`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_192.table.semigroup basis :=
  basis_complete_of_exact Generated.Catalogue.S5_192.table
    models valid_exactBasisClass

/-- Unconditional reverse-word endpoint for the opposite of `S5_192`. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_192.table.semigroup.opposite
      (reversedBasis basis) :=
  basis_complete.oppositeReversed

end S5_192

end SemigroupBasis.CoRoots.S5_55Family

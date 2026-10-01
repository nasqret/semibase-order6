import SemigroupBasis.CoRoots.S5_196
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_196Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_196

private def lengthState (marker : Fin 5) (n : Nat) : Fin 5 :=
  if n = 1 then marker else if n = 2 then 1 else 0

private theorem lengthFold
    (mul : Fin 5 → Fin 5 → Fin 5)
    (marker : Fin 5)
    (step :
      ∀ n, 0 < n →
        mul (lengthState marker n) marker =
          lengthState marker (n + 1))
    (xs : List Nat) (acc : Nat) (accPositive : 0 < acc) :
    xs.foldl (fun current _ => mul current marker)
        (lengthState marker acc) =
      lengthState marker (acc + xs.length) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [step acc accPositive, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem lengthState_capped_injective
    (marker : Fin 5)
    (markerNeZero : marker ≠ 0)
    (markerNeOne : marker ≠ 1)
    {m n : Nat} (mPositive : 0 < m) (nPositive : 0 < n)
    (equal : lengthState marker m = lengthState marker n) :
    min m 3 = min n 3 := by
  by_cases hm1 : m = 1
  · subst m
    by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        have markerEq : marker = 1 := by
          simpa [lengthState] using equal
        exact (markerNeOne markerEq).elim
      · have hn3 : 3 ≤ n := by omega
        have markerEq : marker = 0 := by
          simpa [lengthState, hn1, hn2] using equal
        exact (markerNeZero markerEq).elim
  · by_cases hm2 : m = 2
    · subst m
      by_cases hn1 : n = 1
      · subst n
        have markerEq : marker = 1 := by
          simpa [lengthState] using equal.symm
        exact (markerNeOne markerEq).elim
      · by_cases hn2 : n = 2
        · subst n
          rfl
        · have hn3 : 3 ≤ n := by omega
          have values := congrArg Fin.val equal
          simp [lengthState, hn1, hn2] at values
    · have hm3 : 3 ≤ m := by omega
      by_cases hn1 : n = 1
      · subst n
        have markerEq : marker = 0 := by
          simpa [lengthState, hm1, hm2] using equal.symm
        exact (markerNeZero markerEq).elim
      · by_cases hn2 : n = 2
        · subst n
          have values := congrArg Fin.val equal
          simp [lengthState, hm1, hm2] at values
        · have hn3 : 3 ≤ n := by omega
          simp [Nat.min_eq_right hm3, Nat.min_eq_right hn3]

private theorem capped_length_of_eval
    (semigroup : Semigroup (Fin 5))
    (marker : Fin 5)
    (markerNeZero : marker ≠ 0)
    (markerNeOne : marker ≠ 1)
    (evalLength :
      ∀ word : Word Nat,
        semigroup.eval (fun _ => marker) word =
          lengthState marker word.toList.length)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup) :
    min identity.lhs.toList.length 3 =
      min identity.rhs.toList.length 3 := by
  have evaluated := valid (fun _ => marker)
  rw [evalLength, evalLength] at evaluated
  exact lengthState_capped_injective marker
    markerNeZero markerNeOne
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

namespace S5_196

private def markerEmbedding :
    Embedding finalMarkerThree.semigroup
      Generated.Catalogue.S5_196.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨2, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private theorem lengthStep (n : Nat) (positive : 0 < n) :
    Generated.Catalogue.S5_196.mul
        (lengthState 3 n) 3 =
      lengthState 3 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 ≤ n := by omega
      simp [lengthState, hn1, hn2,
        show n ≠ 0 by omega,
        show n + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_196.mul]

private theorem evalLength (word : Word Nat) :
    Generated.Catalogue.S5_196.table.semigroup.eval
        (fun _ => (3 : Fin 5)) word =
      lengthState 3 word.toList.length := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_196.mul current 3)
            3 =
          lengthState 3 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_196.mul 3
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_196.table.semigroup basis :=
  models_of_finite_checks
    Generated.Catalogue.S5_196.table (by decide)

theorem valid_support
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_196.table.semigroup) :
    SameSupport identity.lhs identity.rhs :=
  finalMarkerValid_support identity
    (markerEmbedding.pullback_identity identity valid)

theorem valid_simpleFinal
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_196.table.semigroup) :
    SameSimpleFinal identity.lhs identity.rhs :=
  finalMarkerValid_simpleFinal identity
    (markerEmbedding.pullback_identity identity valid)

theorem valid_capped_length
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_196.table.semigroup) :
    min identity.lhs.toList.length 3 =
      min identity.rhs.toList.length 3 :=
  capped_length_of_eval
    Generated.Catalogue.S5_196.table.semigroup
    3 (by decide) (by decide) evalLength identity valid

/-- The exact `S5_196` table separates precisely the shared syntactic
normal-form classes. -/
theorem valid_exactBasisClass
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_196.table.semigroup) :
    ExactBasisClass identity.lhs identity.rhs :=
  exactBasisClass_of_separates identity
    (valid_support identity valid)
    (valid_simpleFinal identity valid)
    (valid_capped_length identity valid)

/-- Unconditional representative endpoint for `S5_196`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_196.table.semigroup basis :=
  basis_complete_of_exact
    Generated.Catalogue.S5_196.table
    models valid_exactBasisClass

/-- Unconditional reverse-word endpoint for the opposite of `S5_196`. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_196.table.semigroup.opposite
      expectedReversedBasis := by
  rw [← reversedBasis_eq_expected]
  exact basis_complete.oppositeReversed

end S5_196

namespace S5_197

private def markerEmbedding :
    Embedding finalMarkerThree.semigroup
      Generated.Catalogue.S5_197.table.semigroup where
  toFun := fun value =>
    if value.val = 0 then ⟨0, by decide⟩
    else if value.val = 1 then ⟨2, by decide⟩
    else ⟨4, by decide⟩
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

private theorem lengthStep (n : Nat) (positive : 0 < n) :
    Generated.Catalogue.S5_197.mul
        (lengthState 3 n) 3 =
      lengthState 3 (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 ≤ n := by omega
      simp [lengthState, hn1, hn2,
        show n ≠ 0 by omega,
        show n + 1 ≠ 2 by omega,
        Generated.Catalogue.S5_197.mul]

private theorem evalLength (word : Word Nat) :
    Generated.Catalogue.S5_197.table.semigroup.eval
        (fun _ => (3 : Fin 5)) word =
      lengthState 3 word.toList.length := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              Generated.Catalogue.S5_197.mul current 3)
            3 =
          lengthState 3 (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold Generated.Catalogue.S5_197.mul 3
          lengthStep tail 1 (by omega)

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_197.table.semigroup basis :=
  models_of_finite_checks
    Generated.Catalogue.S5_197.table (by decide)

theorem valid_support
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_197.table.semigroup) :
    SameSupport identity.lhs identity.rhs :=
  finalMarkerValid_support identity
    (markerEmbedding.pullback_identity identity valid)

theorem valid_simpleFinal
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_197.table.semigroup) :
    SameSimpleFinal identity.lhs identity.rhs :=
  finalMarkerValid_simpleFinal identity
    (markerEmbedding.pullback_identity identity valid)

theorem valid_capped_length
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_197.table.semigroup) :
    min identity.lhs.toList.length 3 =
      min identity.rhs.toList.length 3 :=
  capped_length_of_eval
    Generated.Catalogue.S5_197.table.semigroup
    3 (by decide) (by decide) evalLength identity valid

/-- The exact `S5_197` table separates precisely the shared syntactic
normal-form classes. -/
theorem valid_exactBasisClass
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_197.table.semigroup) :
    ExactBasisClass identity.lhs identity.rhs :=
  exactBasisClass_of_separates identity
    (valid_support identity valid)
    (valid_simpleFinal identity valid)
    (valid_capped_length identity valid)

/-- Unconditional representative endpoint for `S5_197`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_197.table.semigroup basis :=
  basis_complete_of_exact
    Generated.Catalogue.S5_197.table
    models valid_exactBasisClass

/-- Unconditional reverse-word endpoint for the opposite of `S5_197`. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_197.table.semigroup.opposite
      expectedReversedBasis := by
  rw [← reversedBasis_eq_expected]
  exact basis_complete.oppositeReversed

end S5_197

end SemigroupBasis.CoRoots.S5_196Family

import SemigroupBasis.Examples.CommutativeIndexFourFive
import SemigroupBasis.Generated.CatalogueOrder5Part02
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_217

open SemigroupBasis
open SemigroupBasis.Examples

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_217.table

abbrev basis : List (Identity Nat) :=
  commutativeIndexFourFiveBasis

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_217.table := rfl

private theorem mul_commutative (a b : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_217.mul a b =
      SemigroupBasis.Generated.Catalogue.S5_217.mul b a := by
  decide +revert

private theorem mul_power (a : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_217.mul
        (SemigroupBasis.Generated.Catalogue.S5_217.mul
          (SemigroupBasis.Generated.Catalogue.S5_217.mul a a) a) a =
      SemigroupBasis.Generated.Catalogue.S5_217.mul
        (SemigroupBasis.Generated.Catalogue.S5_217.mul
          (SemigroupBasis.Generated.Catalogue.S5_217.mul
            (SemigroupBasis.Generated.Catalogue.S5_217.mul a a) a) a) a := by
  decide +revert

/-- The exact catalogue table satisfies `xy = yx`, `xxxx = xxxxx`. -/
theorem models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, commutativeIndexFourFiveBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro valuation
    change
      SemigroupBasis.Generated.Catalogue.S5_217.mul
          (valuation 0) (valuation 1) =
        SemigroupBasis.Generated.Catalogue.S5_217.mul
          (valuation 1) (valuation 0)
    exact mul_commutative (valuation 0) (valuation 1)
  · intro valuation
    change
      SemigroupBasis.Generated.Catalogue.S5_217.mul
          (SemigroupBasis.Generated.Catalogue.S5_217.mul
            (SemigroupBasis.Generated.Catalogue.S5_217.mul
              (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 0) =
        SemigroupBasis.Generated.Catalogue.S5_217.mul
          (SemigroupBasis.Generated.Catalogue.S5_217.mul
            (SemigroupBasis.Generated.Catalogue.S5_217.mul
              (SemigroupBasis.Generated.Catalogue.S5_217.mul
                (valuation 0) (valuation 0))
              (valuation 0))
            (valuation 0))
          (valuation 0)
    exact mul_power (valuation 0)

/-- Assign the distinguished variable to one-based element 4 and every
other variable to the identity element 5. -/
def countSeparator (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then 3 else 4

/-- The five table states corresponding to capped exponents zero through
four are one-based elements `5, 4, 2, 3, 1`. -/
def cappedCountState (n : Nat) : Fin 5 :=
  if n = 0 then 4
  else if n = 1 then 3
  else if n = 2 then 1
  else if n = 3 then 2
  else 0

private theorem mul_state_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_217.mul
        (cappedCountState n) 3 =
      cappedCountState (n + 1) := by
  by_cases h0 : n = 0
  · subst n
    rfl
  · by_cases h1 : n = 1
    · subst n
      rfl
    · by_cases h2 : n = 2
      · subst n
        rfl
      · by_cases h3 : n = 3
        · subst n
          rfl
        · have hn : 4 ≤ n := by omega
          have hn0 : n + 1 ≠ 0 := by omega
          have hn1 : n + 1 ≠ 1 := by omega
          have hn2 : n + 1 ≠ 2 := by omega
          have hn3 : n + 1 ≠ 3 := by omega
          simp [cappedCountState, h0, h1, h2, h3,
            hn0, hn1, hn2, hn3,
            SemigroupBasis.Generated.Catalogue.S5_217.mul]

private theorem mul_identity (a : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_217.mul a 4 = a := by
  decide +revert

theorem identityElementFive_certificate (a : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_217.mul a 4 = a ∧
      SemigroupBasis.Generated.Catalogue.S5_217.mul 4 a = a := by
  decide +revert

theorem countSeparatorFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          SemigroupBasis.Generated.Catalogue.S5_217.mul current
            (countSeparator z x))
        (cappedCountState acc) =
      cappedCountState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show countSeparator z z = (3 : Fin 5) by
          simp [countSeparator]]
        rw [mul_state_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show countSeparator z x = (4 : Fin 5) by
          simp [countSeparator, hx]]
        rw [mul_identity, ih]

theorem eval_countSeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (countSeparator z) word =
      cappedCountState (word.toList.count z) := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              SemigroupBasis.Generated.Catalogue.S5_217.mul current
                (countSeparator z x))
            (countSeparator z head) =
          cappedCountState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show countSeparator z z = cappedCountState 1 by
          apply Fin.ext
          simp [countSeparator, cappedCountState]]
        rw [countSeparatorFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show countSeparator z head = cappedCountState 0 by
          apply Fin.ext
          simp [countSeparator, cappedCountState, hhead]]
        rw [countSeparatorFold]
        congr 1
        omega

private theorem cappedCountState_injective
    {m n : Nat}
    (hm : cappedCountState m = cappedCountState n) :
    min m 4 = min n 4 := by
  have values := congrArg Fin.val hm
  by_cases hm0 : m = 0 <;>
    by_cases hm1 : m = 1 <;>
    by_cases hm2 : m = 2 <;>
    by_cases hm3 : m = 3 <;>
    by_cases hn0 : n = 0 <;>
    by_cases hn1 : n = 1 <;>
    by_cases hn2 : n = 2 <;>
    by_cases hn3 : n = 3 <;>
    simp [cappedCountState, hm0, hm1, hm2, hm3,
      hn0, hn1, hn2, hn3] at values ⊢ <;>
    omega

/-- Every identity valid in the exact table preserves each variable's
multiplicity after capping at four. -/
theorem valid_capped_count
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, min (identity.lhs.toList.count z) 4 =
      min (identity.rhs.toList.count z) 4 := by
  intro z
  have evaluated := valid (countSeparator z)
  rw [eval_countSeparator, eval_countSeparator] at evaluated
  exact cappedCountState_injective evaluated

/-- Derivability from the exact basis is exactly capped coordinate equality. -/
theorem derives_iff_sameCappedFour {u v : Word Nat} :
    Derives basis u v ↔ SameCappedFour u v := by
  constructor
  · intro derivation z
    have valid : (Identity.mk u v).SatisfiedBy table.semigroup := by
      intro valuation
      exact Derives.sound models derivation valuation
    exact valid_capped_count ⟨u, v⟩ valid z
  · exact indexFourFiveDerives_of_sameCappedFour u v

/-- Powers are computed from the one-based identity element 5. -/
def tablePower (a : Fin 5) : Nat → Fin 5
  | 0 => 4
  | n + 1 =>
      SemigroupBasis.Generated.Catalogue.S5_217.mul
        (tablePower a n) a

def canonicalPowerProfileOneBased (n : Nat) : List Nat :=
  List.ofFn fun a : Fin 5 => (tablePower a n).val + 1

/-- The exact one-based unary power profiles from the authoritative
structural certificate. -/
def canonicalPowerProfilesOneBased : List (List Nat) :=
  [[5, 5, 5, 5, 5],
    [1, 2, 3, 4, 5],
    [1, 1, 1, 2, 5],
    [1, 1, 1, 3, 5],
    [1, 1, 1, 1, 5]]

theorem canonicalPowerProfilesOneBased_certificate :
    [canonicalPowerProfileOneBased 0,
      canonicalPowerProfileOneBased 1,
      canonicalPowerProfileOneBased 2,
      canonicalPowerProfileOneBased 3,
      canonicalPowerProfileOneBased 4] =
        canonicalPowerProfilesOneBased := by
  decide

theorem cappedCountStatesOneBased_certificate :
    [(cappedCountState 0).val + 1,
      (cappedCountState 1).val + 1,
      (cappedCountState 2).val + 1,
      (cappedCountState 3).val + 1,
      (cappedCountState 4).val + 1] =
        [5, 4, 2, 3, 1] := by
  decide

/-- Unconditional completeness for the exact stored table. -/
theorem basis_complete : BasisFor table.semigroup basis :=
  commutativeIndexFourFiveBasis_complete_of_separates
    table models valid_capped_count

theorem representative_basis : BasisFor table.semigroup basis :=
  basis_complete

theorem self_dual :
    table.semigroup.opposite = table.semigroup := by
  unfold table SemigroupBasis.Generated.Catalogue.S5_217.table
    SemigroupBasis.Generated.Catalogue.S5_217.mul
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite basis := by
  rw [self_dual]
  exact basis_complete

theorem opposite_basis :
    BasisFor table.semigroup.opposite basis :=
  opposite_basis_complete

end SemigroupBasis.CoRoots.S5_217

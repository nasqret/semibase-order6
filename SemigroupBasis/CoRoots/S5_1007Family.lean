import SemigroupBasis.CoRoots.S5_1007
import SemigroupBasis.Generated.CatalogueOrder5Part08
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_1007Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_1007

private theorem modelsOfPowerAndCommutativity
    (T : FiniteTable)
    (power :
      ∀ a : Fin T.order,
        a =
          T.mul
            (T.mul
              (T.mul
                (T.mul
                  (T.mul
                    (T.mul a a)
                    a)
                  a)
                a)
              a)
            a
    )
    (commutative :
      ∀ a b : Fin T.order, T.mul a b = T.mul b a) :
    Models T.semigroup basis := by
  intro identity member
  simp only [basis, commutativePositiveModSixBasis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro valuation
    change valuation 0 =
      T.mul
        (T.mul
          (T.mul
            (T.mul
              (T.mul
                (T.mul (valuation 0) (valuation 0))
                (valuation 0))
              (valuation 0))
            (valuation 0))
          (valuation 0))
        (valuation 0)
    exact power (valuation 0)
  · intro valuation
    change T.mul (valuation 0) (valuation 1) =
      T.mul (valuation 1) (valuation 0)
    exact commutative (valuation 0) (valuation 1)

namespace S5_1007

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1007.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_1007.table := rfl

private theorem power (a : Fin 5) :
    a =
      SemigroupBasis.Generated.Catalogue.S5_1007.mul
        (SemigroupBasis.Generated.Catalogue.S5_1007.mul
          (SemigroupBasis.Generated.Catalogue.S5_1007.mul
            (SemigroupBasis.Generated.Catalogue.S5_1007.mul
              (SemigroupBasis.Generated.Catalogue.S5_1007.mul
                (SemigroupBasis.Generated.Catalogue.S5_1007.mul a a)
                a)
              a)
            a)
          a)
        a := by
  decide +revert

private theorem commutative (a b : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_1007.mul a b =
      SemigroupBasis.Generated.Catalogue.S5_1007.mul b a := by
  decide +revert

theorem models : Models table.semigroup basis :=
  modelsOfPowerAndCommutativity table power commutative

def paritySeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 1 0 z

private theorem parityMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1007.mul
        (positiveModSixParityState n) 1 =
      positiveModSixParityState (n + 1) := by
  by_cases h0 : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by
      omega
    simp [positiveModSixParityState, h0, hnext,
      SemigroupBasis.Generated.Catalogue.S5_1007.mul]
  · have h1 : n % 2 = 1 := by
      omega
    have hnext : (n + 1) % 2 = 0 := by
      omega
    simp [positiveModSixParityState, h0, h1, hnext,
      SemigroupBasis.Generated.Catalogue.S5_1007.mul]

private theorem parityMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1007.mul
        (positiveModSixParityState n) 0 =
      positiveModSixParityState n := by
  by_cases h0 : n % 2 = 0
  · simp [positiveModSixParityState, h0,
      SemigroupBasis.Generated.Catalogue.S5_1007.mul]
  · have h1 : n % 2 = 1 := by
      omega
    simp [positiveModSixParityState, h0, h1,
      SemigroupBasis.Generated.Catalogue.S5_1007.mul]

theorem eval_paritySeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (paritySeparator z) word =
      positiveModSixParityState (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup positiveModSixParityState
      1 0 (by rfl) (by rfl) parityMul_target parityMul_other
      z word

def ternarySeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 3 2 z

private theorem ternaryMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1007.mul
        (positiveModSixTernaryState n) 3 =
      positiveModSixTernaryState (n + 1) := by
  by_cases h0 : n % 3 = 0
  · have hnext : (n + 1) % 3 = 1 := by
      omega
    simp [positiveModSixTernaryState, h0, hnext,
      SemigroupBasis.Generated.Catalogue.S5_1007.mul]
  · by_cases h1 : n % 3 = 1
    · have hnext : (n + 1) % 3 = 2 := by
        omega
      simp [positiveModSixTernaryState, h0, h1, hnext,
        SemigroupBasis.Generated.Catalogue.S5_1007.mul]
    · have h2 : n % 3 = 2 := by
        omega
      have hnext : (n + 1) % 3 = 0 := by
        omega
      simp [positiveModSixTernaryState, h0, h1, h2, hnext,
        SemigroupBasis.Generated.Catalogue.S5_1007.mul]

private theorem ternaryMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1007.mul
        (positiveModSixTernaryState n) 2 =
      positiveModSixTernaryState n := by
  by_cases h0 : n % 3 = 0
  · simp [positiveModSixTernaryState, h0,
      SemigroupBasis.Generated.Catalogue.S5_1007.mul]
  · by_cases h1 : n % 3 = 1
    · simp [positiveModSixTernaryState, h0, h1,
        SemigroupBasis.Generated.Catalogue.S5_1007.mul]
    · have h2 : n % 3 = 2 := by
        omega
      simp [positiveModSixTernaryState, h0, h1, h2,
        SemigroupBasis.Generated.Catalogue.S5_1007.mul]

theorem eval_ternarySeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (ternarySeparator z) word =
      positiveModSixTernaryState (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup positiveModSixTernaryState
      3 2 (by rfl) (by rfl) ternaryMul_target ternaryMul_other
      z word

def supportSeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 0 2 z

private theorem supportMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1007.mul
        (supportState 2 0 n) 0 =
      supportState 2 0 (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn, show n + 1 ≠ 0 by omega,
      SemigroupBasis.Generated.Catalogue.S5_1007.mul]

private theorem supportMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1007.mul
        (supportState 2 0 n) 2 =
      supportState 2 0 n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn,
      SemigroupBasis.Generated.Catalogue.S5_1007.mul]

theorem eval_supportSeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (supportSeparator z) word =
      supportState 2 0 (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup (supportState 2 0)
      0 2 (by rfl) (by rfl) supportMul_target supportMul_other
      z word

theorem valid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  exact support_iff_of_state_eq 2 0 (by decide)
    z identity.lhs.toList identity.rhs.toList evaluated

theorem valid_count_mod_six
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, identity.lhs.toList.count z % 6 =
      identity.rhs.toList.count z % 6 := by
  intro z
  have parityEvaluated := valid (paritySeparator z)
  rw [eval_paritySeparator, eval_paritySeparator] at parityEvaluated
  have ternaryEvaluated := valid (ternarySeparator z)
  rw [eval_ternarySeparator, eval_ternarySeparator] at ternaryEvaluated
  exact modSix_eq_of_modTwo_modThree_eq
    (modTwo_eq_of_parityState_eq parityEvaluated)
    (modThree_eq_of_ternaryState_eq ternaryEvaluated)

theorem valid_samePositiveModSix
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SamePositiveModSix identity.lhs identity.rhs :=
  ⟨valid_support identity valid, valid_count_mod_six identity valid⟩

theorem derives_iff_samePositiveModSix {u v : Word Nat} :
    Derives basis u v ↔ SamePositiveModSix u v := by
  constructor
  · intro derivation
    have valid : (Identity.mk u v).SatisfiedBy table.semigroup := by
      intro valuation
      exact Derives.sound models derivation valuation
    exact valid_samePositiveModSix ⟨u, v⟩ valid
  · exact commutativePositiveModSixDerives_of_invariant

/-- The exact catalogue representative `S5_1007` has basis
`x = xxxxxxx`, `xy = yx`. -/
theorem basis_complete : BasisFor table.semigroup basis :=
  commutativePositiveModSixBasis_complete_of_separates
    table models valid_support valid_count_mod_six

theorem representative_basis : BasisFor table.semigroup basis :=
  basis_complete

theorem self_dual :
    table.semigroup.opposite = table.semigroup := by
  unfold table SemigroupBasis.Generated.Catalogue.S5_1007.table
    SemigroupBasis.Generated.Catalogue.S5_1007.mul
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

end S5_1007

namespace S5_1008

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1008.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_1008.table := rfl

private theorem power (a : Fin 5) :
    a =
      SemigroupBasis.Generated.Catalogue.S5_1008.mul
        (SemigroupBasis.Generated.Catalogue.S5_1008.mul
          (SemigroupBasis.Generated.Catalogue.S5_1008.mul
            (SemigroupBasis.Generated.Catalogue.S5_1008.mul
              (SemigroupBasis.Generated.Catalogue.S5_1008.mul
                (SemigroupBasis.Generated.Catalogue.S5_1008.mul a a)
                a)
              a)
            a)
          a)
        a := by
  decide +revert

private theorem commutative (a b : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_1008.mul a b =
      SemigroupBasis.Generated.Catalogue.S5_1008.mul b a := by
  decide +revert

theorem models : Models table.semigroup basis :=
  modelsOfPowerAndCommutativity table power commutative

def paritySeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 1 0 z

private theorem parityMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1008.mul
        (positiveModSixParityState n) 1 =
      positiveModSixParityState (n + 1) := by
  by_cases h0 : n % 2 = 0
  · have hnext : (n + 1) % 2 = 1 := by
      omega
    simp [positiveModSixParityState, h0, hnext,
      SemigroupBasis.Generated.Catalogue.S5_1008.mul]
  · have h1 : n % 2 = 1 := by
      omega
    have hnext : (n + 1) % 2 = 0 := by
      omega
    simp [positiveModSixParityState, h0, h1, hnext,
      SemigroupBasis.Generated.Catalogue.S5_1008.mul]

private theorem parityMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1008.mul
        (positiveModSixParityState n) 0 =
      positiveModSixParityState n := by
  by_cases h0 : n % 2 = 0
  · simp [positiveModSixParityState, h0,
      SemigroupBasis.Generated.Catalogue.S5_1008.mul]
  · have h1 : n % 2 = 1 := by
      omega
    simp [positiveModSixParityState, h0, h1,
      SemigroupBasis.Generated.Catalogue.S5_1008.mul]

theorem eval_paritySeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (paritySeparator z) word =
      positiveModSixParityState (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup positiveModSixParityState
      1 0 (by rfl) (by rfl) parityMul_target parityMul_other
      z word

def ternarySeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 3 2 z

private theorem ternaryMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1008.mul
        (positiveModSixTernaryState n) 3 =
      positiveModSixTernaryState (n + 1) := by
  by_cases h0 : n % 3 = 0
  · have hnext : (n + 1) % 3 = 1 := by
      omega
    simp [positiveModSixTernaryState, h0, hnext,
      SemigroupBasis.Generated.Catalogue.S5_1008.mul]
  · by_cases h1 : n % 3 = 1
    · have hnext : (n + 1) % 3 = 2 := by
        omega
      simp [positiveModSixTernaryState, h0, h1, hnext,
        SemigroupBasis.Generated.Catalogue.S5_1008.mul]
    · have h2 : n % 3 = 2 := by
        omega
      have hnext : (n + 1) % 3 = 0 := by
        omega
      simp [positiveModSixTernaryState, h0, h1, h2, hnext,
        SemigroupBasis.Generated.Catalogue.S5_1008.mul]

private theorem ternaryMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1008.mul
        (positiveModSixTernaryState n) 2 =
      positiveModSixTernaryState n := by
  by_cases h0 : n % 3 = 0
  · simp [positiveModSixTernaryState, h0,
      SemigroupBasis.Generated.Catalogue.S5_1008.mul]
  · by_cases h1 : n % 3 = 1
    · simp [positiveModSixTernaryState, h0, h1,
        SemigroupBasis.Generated.Catalogue.S5_1008.mul]
    · have h2 : n % 3 = 2 := by
        omega
      simp [positiveModSixTernaryState, h0, h1, h2,
        SemigroupBasis.Generated.Catalogue.S5_1008.mul]

theorem eval_ternarySeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (ternarySeparator z) word =
      positiveModSixTernaryState (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup positiveModSixTernaryState
      3 2 (by rfl) (by rfl) ternaryMul_target ternaryMul_other
      z word

def supportSeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 2 0 z

private theorem supportMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1008.mul
        (supportState 0 2 n) 2 =
      supportState 0 2 (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn, show n + 1 ≠ 0 by omega,
      SemigroupBasis.Generated.Catalogue.S5_1008.mul]

private theorem supportMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_1008.mul
        (supportState 0 2 n) 0 =
      supportState 0 2 n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn,
      SemigroupBasis.Generated.Catalogue.S5_1008.mul]

theorem eval_supportSeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (supportSeparator z) word =
      supportState 0 2 (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup (supportState 0 2)
      2 0 (by rfl) (by rfl) supportMul_target supportMul_other
      z word

theorem valid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  exact support_iff_of_state_eq 0 2 (by decide)
    z identity.lhs.toList identity.rhs.toList evaluated

theorem valid_count_mod_six
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, identity.lhs.toList.count z % 6 =
      identity.rhs.toList.count z % 6 := by
  intro z
  have parityEvaluated := valid (paritySeparator z)
  rw [eval_paritySeparator, eval_paritySeparator] at parityEvaluated
  have ternaryEvaluated := valid (ternarySeparator z)
  rw [eval_ternarySeparator, eval_ternarySeparator] at ternaryEvaluated
  exact modSix_eq_of_modTwo_modThree_eq
    (modTwo_eq_of_parityState_eq parityEvaluated)
    (modThree_eq_of_ternaryState_eq ternaryEvaluated)

theorem valid_samePositiveModSix
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SamePositiveModSix identity.lhs identity.rhs :=
  ⟨valid_support identity valid, valid_count_mod_six identity valid⟩

theorem derives_iff_samePositiveModSix {u v : Word Nat} :
    Derives basis u v ↔ SamePositiveModSix u v := by
  constructor
  · intro derivation
    have valid : (Identity.mk u v).SatisfiedBy table.semigroup := by
      intro valuation
      exact Derives.sound models derivation valuation
    exact valid_samePositiveModSix ⟨u, v⟩ valid
  · exact commutativePositiveModSixDerives_of_invariant

/-- The exact catalogue representative `S5_1008` has basis
`x = xxxxxxx`, `xy = yx`. -/
theorem basis_complete : BasisFor table.semigroup basis :=
  commutativePositiveModSixBasis_complete_of_separates
    table models valid_support valid_count_mod_six

theorem representative_basis : BasisFor table.semigroup basis :=
  basis_complete

theorem self_dual :
    table.semigroup.opposite = table.semigroup := by
  unfold table SemigroupBasis.Generated.Catalogue.S5_1008.table
    SemigroupBasis.Generated.Catalogue.S5_1008.mul
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

end S5_1008

structure FamilyBasisEndpoints : Prop where
  s5_1007_representative :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1007.table.semigroup basis
  s5_1007_opposite :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1007.table.semigroup.opposite
      basis
  s5_1008_representative :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1008.table.semigroup basis
  s5_1008_opposite :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_1008.table.semigroup.opposite
      basis

theorem family_basis_endpoints : FamilyBasisEndpoints where
  s5_1007_representative := S5_1007.basis_complete
  s5_1007_opposite := S5_1007.opposite_basis_complete
  s5_1008_representative := S5_1008.basis_complete
  s5_1008_opposite := S5_1008.opposite_basis_complete

end SemigroupBasis.CoRoots.S5_1007Family

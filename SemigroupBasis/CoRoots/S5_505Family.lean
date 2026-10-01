import SemigroupBasis.CoRoots.S5_505
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_505Family

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_505

private theorem modelsOfPowerAndCommutativity
    (T : FiniteTable)
    (power :
      ∀ a : Fin T.order,
        a =
          T.mul (T.mul (T.mul (T.mul a a) a) a) a
    )
    (commutative :
      ∀ a b : Fin T.order, T.mul a b = T.mul b a) :
    Models T.semigroup basis := by
  intro identity member
  simp only [basis, commutativePositiveModFourBasis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro valuation
    change valuation 0 =
      T.mul
        (T.mul
          (T.mul
            (T.mul (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 0))
        (valuation 0)
    exact power (valuation 0)
  · intro valuation
    change T.mul (valuation 0) (valuation 1) =
      T.mul (valuation 1) (valuation 0)
    exact commutative (valuation 0) (valuation 1)

namespace S5_505

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_505.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_505.table := rfl

private theorem power (a : Fin 5) :
    a =
      SemigroupBasis.Generated.Catalogue.S5_505.mul
        (SemigroupBasis.Generated.Catalogue.S5_505.mul
          (SemigroupBasis.Generated.Catalogue.S5_505.mul
            (SemigroupBasis.Generated.Catalogue.S5_505.mul a a) a)
          a)
        a := by
  decide +revert

private theorem commutative (a b : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_505.mul a b =
      SemigroupBasis.Generated.Catalogue.S5_505.mul b a := by
  decide +revert

theorem models : Models table.semigroup basis :=
  modelsOfPowerAndCommutativity table power commutative

def residueSeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 2 0 z

private theorem residueMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_505.mul
        (positiveModFourResidueState n) 2 =
      positiveModFourResidueState (n + 1) := by
  by_cases h0 : n % 4 = 0
  · have hnext : (n + 1) % 4 = 1 := by
      omega
    simp [positiveModFourResidueState, h0, hnext,
      SemigroupBasis.Generated.Catalogue.S5_505.mul]
  · by_cases h1 : n % 4 = 1
    · have hnext : (n + 1) % 4 = 2 := by
        omega
      simp [positiveModFourResidueState, h0, h1, hnext,
        SemigroupBasis.Generated.Catalogue.S5_505.mul]
    · by_cases h2 : n % 4 = 2
      · have hnext : (n + 1) % 4 = 3 := by
          omega
        simp [positiveModFourResidueState, h0, h1, h2, hnext,
          SemigroupBasis.Generated.Catalogue.S5_505.mul]
      · have h3 : n % 4 = 3 := by
          omega
        have hnext : (n + 1) % 4 = 0 := by
          omega
        simp [positiveModFourResidueState, h0, h1, h2, h3, hnext,
          SemigroupBasis.Generated.Catalogue.S5_505.mul]

private theorem residueMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_505.mul
        (positiveModFourResidueState n) 0 =
      positiveModFourResidueState n := by
  by_cases h0 : n % 4 = 0
  · simp [positiveModFourResidueState, h0,
      SemigroupBasis.Generated.Catalogue.S5_505.mul]
  · by_cases h1 : n % 4 = 1
    · simp [positiveModFourResidueState, h0, h1,
        SemigroupBasis.Generated.Catalogue.S5_505.mul]
    · by_cases h2 : n % 4 = 2
      · simp [positiveModFourResidueState, h0, h1, h2,
          SemigroupBasis.Generated.Catalogue.S5_505.mul]
      · have h3 : n % 4 = 3 := by
          omega
        simp [positiveModFourResidueState, h0, h1, h2, h3,
          SemigroupBasis.Generated.Catalogue.S5_505.mul]

theorem eval_residueSeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (residueSeparator z) word =
      positiveModFourResidueState (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup positiveModFourResidueState
      2 0 (by rfl) (by rfl) residueMul_target residueMul_other
      z word

def supportSeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 0 4 z

private theorem supportMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_505.mul
        (supportState 4 0 n) 0 =
      supportState 4 0 (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn, show n + 1 ≠ 0 by omega,
      SemigroupBasis.Generated.Catalogue.S5_505.mul]

private theorem supportMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_505.mul
        (supportState 4 0 n) 4 =
      supportState 4 0 n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn,
      SemigroupBasis.Generated.Catalogue.S5_505.mul]

theorem eval_supportSeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (supportSeparator z) word =
      supportState 4 0 (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup (supportState 4 0)
      0 4 (by rfl) (by rfl) supportMul_target supportMul_other
      z word

theorem valid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  exact support_iff_of_state_eq 4 0 (by decide)
    z identity.lhs.toList identity.rhs.toList evaluated

theorem valid_count_mod_four
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, identity.lhs.toList.count z % 4 =
      identity.rhs.toList.count z % 4 := by
  intro z
  have evaluated := valid (residueSeparator z)
  rw [eval_residueSeparator, eval_residueSeparator] at evaluated
  exact modFour_eq_of_residueState_eq evaluated

theorem valid_samePositiveModFour
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SamePositiveModFour identity.lhs identity.rhs :=
  ⟨valid_support identity valid, valid_count_mod_four identity valid⟩

theorem derives_iff_samePositiveModFour {u v : Word Nat} :
    Derives basis u v ↔ SamePositiveModFour u v := by
  constructor
  · intro derivation
    have valid : (Identity.mk u v).SatisfiedBy table.semigroup := by
      intro valuation
      exact Derives.sound models derivation valuation
    exact valid_samePositiveModFour ⟨u, v⟩ valid
  · exact commutativePositiveModFourDerives_of_invariant

/-- The exact catalogue representative `S5_505` has basis
`x = xxxxx`, `xy = yx`. -/
theorem basis_complete : BasisFor table.semigroup basis :=
  commutativePositiveModFourBasis_complete_of_separates
    table models valid_support valid_count_mod_four

theorem representative_basis : BasisFor table.semigroup basis :=
  basis_complete

theorem self_dual :
    table.semigroup.opposite = table.semigroup := by
  unfold table SemigroupBasis.Generated.Catalogue.S5_505.table
    SemigroupBasis.Generated.Catalogue.S5_505.mul
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

end S5_505

namespace S5_506

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_506.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S5_506.table := rfl

private theorem power (a : Fin 5) :
    a =
      SemigroupBasis.Generated.Catalogue.S5_506.mul
        (SemigroupBasis.Generated.Catalogue.S5_506.mul
          (SemigroupBasis.Generated.Catalogue.S5_506.mul
            (SemigroupBasis.Generated.Catalogue.S5_506.mul a a) a)
          a)
        a := by
  decide +revert

private theorem commutative (a b : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_506.mul a b =
      SemigroupBasis.Generated.Catalogue.S5_506.mul b a := by
  decide +revert

theorem models : Models table.semigroup basis :=
  modelsOfPowerAndCommutativity table power commutative

def residueSeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 2 0 z

private theorem residueMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_506.mul
        (positiveModFourResidueState n) 2 =
      positiveModFourResidueState (n + 1) := by
  by_cases h0 : n % 4 = 0
  · have hnext : (n + 1) % 4 = 1 := by
      omega
    simp [positiveModFourResidueState, h0, hnext,
      SemigroupBasis.Generated.Catalogue.S5_506.mul]
  · by_cases h1 : n % 4 = 1
    · have hnext : (n + 1) % 4 = 2 := by
        omega
      simp [positiveModFourResidueState, h0, h1, hnext,
        SemigroupBasis.Generated.Catalogue.S5_506.mul]
    · by_cases h2 : n % 4 = 2
      · have hnext : (n + 1) % 4 = 3 := by
          omega
        simp [positiveModFourResidueState, h0, h1, h2, hnext,
          SemigroupBasis.Generated.Catalogue.S5_506.mul]
      · have h3 : n % 4 = 3 := by
          omega
        have hnext : (n + 1) % 4 = 0 := by
          omega
        simp [positiveModFourResidueState, h0, h1, h2, h3, hnext,
          SemigroupBasis.Generated.Catalogue.S5_506.mul]

private theorem residueMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_506.mul
        (positiveModFourResidueState n) 0 =
      positiveModFourResidueState n := by
  by_cases h0 : n % 4 = 0
  · simp [positiveModFourResidueState, h0,
      SemigroupBasis.Generated.Catalogue.S5_506.mul]
  · by_cases h1 : n % 4 = 1
    · simp [positiveModFourResidueState, h0, h1,
        SemigroupBasis.Generated.Catalogue.S5_506.mul]
    · by_cases h2 : n % 4 = 2
      · simp [positiveModFourResidueState, h0, h1, h2,
          SemigroupBasis.Generated.Catalogue.S5_506.mul]
      · have h3 : n % 4 = 3 := by
          omega
        simp [positiveModFourResidueState, h0, h1, h2, h3,
          SemigroupBasis.Generated.Catalogue.S5_506.mul]

theorem eval_residueSeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (residueSeparator z) word =
      positiveModFourResidueState (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup positiveModFourResidueState
      2 0 (by rfl) (by rfl) residueMul_target residueMul_other
      z word

def supportSeparator (z : Nat) : Nat → Fin 5 :=
  countSeparator 4 0 z

private theorem supportMul_target (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_506.mul
        (supportState 0 4 n) 4 =
      supportState 0 4 (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn, show n + 1 ≠ 0 by omega,
      SemigroupBasis.Generated.Catalogue.S5_506.mul]

private theorem supportMul_other (n : Nat) :
    SemigroupBasis.Generated.Catalogue.S5_506.mul
        (supportState 0 4 n) 0 =
      supportState 0 4 n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, hn,
      SemigroupBasis.Generated.Catalogue.S5_506.mul]

theorem eval_supportSeparator (z : Nat) (word : Word Nat) :
    table.semigroup.eval (supportSeparator z) word =
      supportState 0 4 (word.toList.count z) := by
  exact
    evalCountSeparator table.semigroup (supportState 0 4)
      4 0 (by rfl) (by rfl) supportMul_target supportMul_other
      z word

theorem valid_support
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, z ∈ identity.lhs.toList ↔ z ∈ identity.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [eval_supportSeparator, eval_supportSeparator] at evaluated
  exact support_iff_of_state_eq 0 4 (by decide)
    z identity.lhs.toList identity.rhs.toList evaluated

theorem valid_count_mod_four
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, identity.lhs.toList.count z % 4 =
      identity.rhs.toList.count z % 4 := by
  intro z
  have evaluated := valid (residueSeparator z)
  rw [eval_residueSeparator, eval_residueSeparator] at evaluated
  exact modFour_eq_of_residueState_eq evaluated

theorem valid_samePositiveModFour
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SamePositiveModFour identity.lhs identity.rhs :=
  ⟨valid_support identity valid, valid_count_mod_four identity valid⟩

theorem derives_iff_samePositiveModFour {u v : Word Nat} :
    Derives basis u v ↔ SamePositiveModFour u v := by
  constructor
  · intro derivation
    have valid : (Identity.mk u v).SatisfiedBy table.semigroup := by
      intro valuation
      exact Derives.sound models derivation valuation
    exact valid_samePositiveModFour ⟨u, v⟩ valid
  · exact commutativePositiveModFourDerives_of_invariant

/-- The exact catalogue representative `S5_506` has basis
`x = xxxxx`, `xy = yx`. -/
theorem basis_complete : BasisFor table.semigroup basis :=
  commutativePositiveModFourBasis_complete_of_separates
    table models valid_support valid_count_mod_four

theorem representative_basis : BasisFor table.semigroup basis :=
  basis_complete

theorem self_dual :
    table.semigroup.opposite = table.semigroup := by
  unfold table SemigroupBasis.Generated.Catalogue.S5_506.table
    SemigroupBasis.Generated.Catalogue.S5_506.mul
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

end S5_506

structure FamilyBasisEndpoints : Prop where
  s5_505_representative :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_505.table.semigroup basis
  s5_505_opposite :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_505.table.semigroup.opposite
      basis
  s5_506_representative :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_506.table.semigroup basis
  s5_506_opposite :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_506.table.semigroup.opposite
      basis

theorem family_basis_endpoints : FamilyBasisEndpoints where
  s5_505_representative := S5_505.basis_complete
  s5_505_opposite := S5_505.opposite_basis_complete
  s5_506_representative := S5_506.basis_complete
  s5_506_opposite := S5_506.opposite_basis_complete

end SemigroupBasis.CoRoots.S5_505Family

import SemigroupBasis.CoRoots.S5_342Family
import SemigroupBasis.CoRoots.S5_343Family
import SemigroupBasis.CoRoots.S5_344Family
import SemigroupBasis.CoRoots.S5_746
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_62
import SemigroupBasis.Generated.S4_63
import SemigroupBasis.Generated.S4_69
import SemigroupBasis.Generated.S4_70
import SemigroupBasis.Generated.S5_700InflationTransfers
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace SemigroupBasis.Generated.Order6FinalL5TransferV3

open SemigroupBasis

private def checkAssignmentsFused : (variables carrier : Nat) →
    ((Fin variables → Fin carrier) → Bool) → Bool
  | 0, _, predicate => predicate (fun index => Fin.elim0 index)
  | variables + 1, carrier, predicate =>
      (List.finRange carrier).all fun head =>
        checkAssignmentsFused variables carrier fun tail =>
          predicate (Fin.cases head tail)

private theorem checkAssignmentsFused_sound
    (predicate : (Fin variables → Fin carrier) → Bool)
    (checked : checkAssignmentsFused variables carrier predicate = true) :
    ∀ valuation, predicate valuation = true := by
  induction variables with
  | zero =>
      intro valuation
      have valuation_eq :
          valuation = (fun index => Fin.elim0 index) := by
        funext index
        exact Fin.elim0 index
      rw [valuation_eq]
      simpa [checkAssignmentsFused] using checked
  | succ variables ih =>
      intro valuation
      let head : Fin carrier := valuation 0
      let tail : Fin variables → Fin carrier := fun index => valuation index.succ
      change
        (List.finRange carrier).all (fun value =>
          checkAssignmentsFused variables carrier fun candidate =>
            predicate (Fin.cases value candidate)) = true at checked
      have tailChecked :=
        ih (fun candidate => predicate (Fin.cases head candidate))
          ((List.all_eq_true.mp checked) head (List.mem_finRange head)) tail
      have rebuild : Fin.cases head tail = valuation := by
        funext index
        refine Fin.cases ?_ (fun rest => ?_) index
        · rfl
        · rfl
      rw [rebuild] at tailChecked
      exact tailChecked

private def checkIdentityFused (T : FiniteTable)
    (identity : Identity (Fin variables)) : Bool :=
  checkAssignmentsFused variables T.order fun valuation =>
    decide (T.semigroup.eval valuation identity.lhs =
      T.semigroup.eval valuation identity.rhs)

private theorem checkIdentityFused_sound (T : FiniteTable)
    (identity : Identity (Fin variables))
    (checked : checkIdentityFused T identity = true) :
    identity.SatisfiedBy T.semigroup := by
  intro valuation
  exact of_decide_eq_true
    (checkAssignmentsFused_sound
      (fun candidate =>
        decide (T.semigroup.eval candidate identity.lhs =
          T.semigroup.eval candidate identity.rhs)) checked valuation)

private theorem checkIdentityNatFused_sound (T : FiniteTable)
    (identity : Identity (Fin variables))
    (checked : checkIdentityFused T identity = true) :
    (identity.map Fin.val).SatisfiedBy T.semigroup :=
  identity.satisfiedBy_map Fin.val T.semigroup
    (checkIdentityFused_sound T identity checked)

-- BEGIN S6_7270
namespace S6_7270

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,4,4],[1,2,3,4,5,5],[1,2,3,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e355e7ea20d51dc06857521869d530e32d491e34e68bc7d28a17e1785c6480bf"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_62.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_62.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_62.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_62.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7270
-- END S6_7270

-- BEGIN S6_7271
namespace S6_7271

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,4,4],[1,2,3,4,5,6],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4f891c83561dd7a7d49f28d4d25038f2e778f15093942755759d47ab128ceb0d"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_63.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_63.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_63.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_63.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7271
-- END S6_7271

-- BEGIN S6_7273
namespace S6_7273

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,4,4],[1,2,3,5,5,5],[1,2,3,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2d138e8b84192e196dbd42a0e3416cadacdbf1c27d26f917a2f0f2bb78f1067d"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_62.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_62.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_62.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_62.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7273
-- END S6_7273

-- BEGIN S6_7274
namespace S6_7274

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,4,6],[1,2,3,4,5,6],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "716f5888ee14ce2fd96c494f7ae2c45b348a1121f264909ab40e0bed4f1e017d"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_63.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_63.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_63.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_63.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7274
-- END S6_7274

-- BEGIN S6_7280
namespace S6_7280

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[1,2,3,4,5,6],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "14070fd390601e7703013b2c9b9b184bf1216c747e3e65b2fe2805cf77f61cc5"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_63.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_63.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_63.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_63.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7280
-- END S6_7280

-- BEGIN S6_7281
namespace S6_7281

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[1,2,3,4,5,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a404398f8ba509c9e8696b4be64ed731ece2c20483b3eefb7bc0756fb37b91bc"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_746.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_746.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_746.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7281
-- END S6_7281

-- BEGIN S6_7288
namespace S6_7288

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[4,4,4,4,4,4],[4,4,4,4,5,6],[4,4,4,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3fde1f24fbcd9d428554c91420422e11eb50b841f053f135b491c8ff5d9ebfe6"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_753.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_753.table.semigroup targetBasis := by
  exact SemigroupBasis.Generated.S5_700InflationTransfers.S5_753.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7288
-- END S6_7288

-- BEGIN S6_7297
namespace S6_7297

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[1,1,3,1,5,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b9511abb67f744b4ce3f4e8706a66a80692cf20c581612f93474654420a0651a"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = targetLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = targetLaw5 := rfl

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = targetLaw6 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl
  · subst e
    rw [← finiteLaw4_map]
    apply checkIdentityNatFused_sound table finiteLaw4
    rfl
  · subst e
    rw [← finiteLaw5_map]
    apply checkIdentityNatFused_sound table finiteLaw5
    rfl
  · subst e
    rw [← finiteLaw6_map]
    apply checkIdentityNatFused_sound table finiteLaw6
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_69.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_69.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_7297
-- END S6_7297

-- BEGIN S6_7298
namespace S6_7298

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[1,1,3,1,5,1],[1,2,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "34d640c8210dc702d909b290515b92019dc4ce027e0813bf267d737406cd94b5"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = targetLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = targetLaw5 := rfl

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = targetLaw6 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl
  · subst e
    rw [← finiteLaw4_map]
    apply checkIdentityNatFused_sound table finiteLaw4
    rfl
  · subst e
    rw [← finiteLaw5_map]
    apply checkIdentityNatFused_sound table finiteLaw5
    rfl
  · subst e
    rw [← finiteLaw6_map]
    apply checkIdentityNatFused_sound table finiteLaw6
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_69.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_69.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7298
-- END S6_7298

-- BEGIN S6_7299
namespace S6_7299

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[1,1,3,1,5,3],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0da32ec0197121d6e6dab23f8c3b44125c43a0768c9644c93e8bc2a16a5e1095"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = targetLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = targetLaw5 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl
  · subst e
    rw [← finiteLaw4_map]
    apply checkIdentityNatFused_sound table finiteLaw4
    rfl
  · subst e
    rw [← finiteLaw5_map]
    apply checkIdentityNatFused_sound table finiteLaw5
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_70.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_70.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_7299
-- END S6_7299

-- BEGIN S6_7300
namespace S6_7300

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[1,1,3,1,5,3],[1,2,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d08cfa2be00fe4faee411b2708fffb584cd0bc5a55b932b7f5cdd01d5806c146"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = targetLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = targetLaw5 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl
  · subst e
    rw [← finiteLaw4_map]
    apply checkIdentityNatFused_sound table finiteLaw4
    rfl
  · subst e
    rw [← finiteLaw5_map]
    apply checkIdentityNatFused_sound table finiteLaw5
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_70.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_70.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7300
-- END S6_7300

-- BEGIN S6_7307
namespace S6_7307

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[1,2,3,1,5,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b93bf326e46119a04c2c25874d4708e8151d037bf072cdc99b7cfd992828c042"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = targetLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = targetLaw5 := rfl

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = targetLaw6 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl
  · subst e
    rw [← finiteLaw4_map]
    apply checkIdentityNatFused_sound table finiteLaw4
    rfl
  · subst e
    rw [← finiteLaw5_map]
    apply checkIdentityNatFused_sound table finiteLaw5
    rfl
  · subst e
    rw [← finiteLaw6_map]
    apply checkIdentityNatFused_sound table finiteLaw6
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_69.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_69.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7307
-- END S6_7307

-- BEGIN S6_7308
namespace S6_7308

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[1,2,3,1,5,3],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e57ca5bba1b242295858479d4bb740913e982b80b8bc673115577c83752a6e4f"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = targetLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = targetLaw5 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl
  · subst e
    rw [← finiteLaw4_map]
    apply checkIdentityNatFused_sound table finiteLaw4
    rfl
  · subst e
    rw [← finiteLaw5_map]
    apply checkIdentityNatFused_sound table finiteLaw5
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_70.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_70.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7308
-- END S6_7308

-- BEGIN S6_7314
namespace S6_7314

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[5,5,5,5,5,5],[1,2,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e0f0cf21eefbe3f865d9b0bc914c1df79871300d6333a6c922e3216dcba8ef9a"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_342.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 1, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 1, 2]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = targetLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = targetLaw5 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl
  · subst e
    rw [← finiteLaw4_map]
    apply checkIdentityNatFused_sound table finiteLaw4
    rfl
  · subst e
    rw [← finiteLaw5_map]
    apply checkIdentityNatFused_sound table finiteLaw5
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_342.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_342Family.S5_342.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7314
-- END S6_7314

-- BEGIN S6_7315
namespace S6_7315

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[5,5,5,5,5,5],[1,2,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1cb61f195a9cae8626b04ed403b71d5048747b4767b16d201955250a28e12698"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_343.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [1, 1, 2]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_343.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_343Family.S5_343.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7315
-- END S6_7315

-- BEGIN S6_7316
namespace S6_7316

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,1,1,4,1,1],[5,5,5,5,5,5],[1,2,3,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2e52930385a599abe4494e8be6635dde2fc8c959399ea2062835ef57712b650e"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def finiteLaw8 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = targetLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = targetLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = targetLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = targetLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = targetLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = targetLaw5 := rfl

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = targetLaw6 := rfl

theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = targetLaw7 := rfl

theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = targetLaw8 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    apply checkIdentityNatFused_sound table finiteLaw0
    rfl
  · subst e
    rw [← finiteLaw1_map]
    apply checkIdentityNatFused_sound table finiteLaw1
    rfl
  · subst e
    rw [← finiteLaw2_map]
    apply checkIdentityNatFused_sound table finiteLaw2
    rfl
  · subst e
    rw [← finiteLaw3_map]
    apply checkIdentityNatFused_sound table finiteLaw3
    rfl
  · subst e
    rw [← finiteLaw4_map]
    apply checkIdentityNatFused_sound table finiteLaw4
    rfl
  · subst e
    rw [← finiteLaw5_map]
    apply checkIdentityNatFused_sound table finiteLaw5
    rfl
  · subst e
    rw [← finiteLaw6_map]
    apply checkIdentityNatFused_sound table finiteLaw6
    rfl
  · subst e
    rw [← finiteLaw7_map]
    apply checkIdentityNatFused_sound table finiteLaw7
    rfl
  · subst e
    rw [← finiteLaw8_map]
    apply checkIdentityNatFused_sound table finiteLaw8
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_344.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_344Family.S5_344.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7316
-- END S6_7316

end SemigroupBasis.Generated.Order6FinalL5TransferV3

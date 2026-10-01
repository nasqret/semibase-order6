import SemigroupBasis.CoRoots.S5_343Family
import SemigroupBasis.CoRoots.S5_345Family
import SemigroupBasis.CoRoots.S5_381Family
import SemigroupBasis.CoRoots.S5_441Family
import SemigroupBasis.CoRoots.S5_442Completeness
import SemigroupBasis.CoRoots.S5_443Family
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_69
import SemigroupBasis.Generated.S4_70
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

-- BEGIN S6_6303
namespace S6_6303

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,2,4,4,1],[1,2,2,4,4,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "fab245aba5d2c45ffcb268088793caa9bd822ee176fc0e8edd10a237002e98b6"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
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

end S6_6303
-- END S6_6303

-- BEGIN S6_6304
namespace S6_6304

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,2,4,4,2],[1,2,2,4,4,2],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0e8d354cd968f8f36c796aa625e4f0d0d442d8ae4c868b8373cb3f6481c67739"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
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

end S6_6304
-- END S6_6304

-- BEGIN S6_6309
namespace S6_6309

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,2,4,4,4],[1,2,2,4,4,5],[1,2,2,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d69d00a299d7db113fa05deb1a016da3f70fe49591fc68931660c4989052e9c2"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
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
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7]

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

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
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

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = targetLaw6 := rfl

theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = targetLaw7 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_381Family.S5_610.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6309
-- END S6_6309

-- BEGIN S6_6311
namespace S6_6311

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,2,4,4,4],[1,2,2,4,4,5],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d7dc0d331832afe5adc2e06b6affbd223dfaac5a5e6e97790645d4390f894887"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
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
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7]

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

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
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

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = targetLaw6 := rfl

theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = targetLaw7 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_381Family.S5_610.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6311
-- END S6_6311

-- BEGIN S6_6313
namespace S6_6313

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,2,4,5,1],[1,2,2,5,4,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b8234a734aefc65142c4e77a6268ac06f9581f118222a62fc86bc350d1f955d8"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_612.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0, 1, 1]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0, 1]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0, 1]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 1, 0, 0]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 1]⟩⟩

def targetLaw16 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw17 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw18 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw19 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw20 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨1, [0, 1, 2, 1]⟩⟩

def targetLaw21 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩

def targetLaw22 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def targetLaw23 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [2, 0, 1, 1]⟩⟩

def targetLaw24 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15, targetLaw16, targetLaw17, targetLaw18, targetLaw19, targetLaw20, targetLaw21, targetLaw22, targetLaw23, targetLaw24]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def finiteLaw7 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

def finiteLaw8 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0, 1, 1]⟩⟩

def finiteLaw9 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0, 1]⟩⟩

def finiteLaw10 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def finiteLaw11 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0, 1]⟩⟩

def finiteLaw12 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def finiteLaw13 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 1, 0, 0]⟩⟩

def finiteLaw14 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw15 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 1]⟩⟩

def finiteLaw16 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw17 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw18 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw20 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨1, [0, 1, 2, 1]⟩⟩

def finiteLaw21 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩

def finiteLaw22 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def finiteLaw23 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [2, 0, 1, 1]⟩⟩

def finiteLaw24 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩

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

theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = targetLaw9 := rfl

theorem finiteLaw10_map :
    finiteLaw10.map Fin.val = targetLaw10 := rfl

theorem finiteLaw11_map :
    finiteLaw11.map Fin.val = targetLaw11 := rfl

theorem finiteLaw12_map :
    finiteLaw12.map Fin.val = targetLaw12 := rfl

theorem finiteLaw13_map :
    finiteLaw13.map Fin.val = targetLaw13 := rfl

theorem finiteLaw14_map :
    finiteLaw14.map Fin.val = targetLaw14 := rfl

theorem finiteLaw15_map :
    finiteLaw15.map Fin.val = targetLaw15 := rfl

theorem finiteLaw16_map :
    finiteLaw16.map Fin.val = targetLaw16 := rfl

theorem finiteLaw17_map :
    finiteLaw17.map Fin.val = targetLaw17 := rfl

theorem finiteLaw18_map :
    finiteLaw18.map Fin.val = targetLaw18 := rfl

theorem finiteLaw19_map :
    finiteLaw19.map Fin.val = targetLaw19 := rfl

theorem finiteLaw20_map :
    finiteLaw20.map Fin.val = targetLaw20 := rfl

theorem finiteLaw21_map :
    finiteLaw21.map Fin.val = targetLaw21 := rfl

theorem finiteLaw22_map :
    finiteLaw22.map Fin.val = targetLaw22 := rfl

theorem finiteLaw23_map :
    finiteLaw23.map Fin.val = targetLaw23 := rfl

theorem finiteLaw24_map :
    finiteLaw24.map Fin.val = targetLaw24 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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
  · subst e
    rw [← finiteLaw9_map]
    apply checkIdentityNatFused_sound table finiteLaw9
    rfl
  · subst e
    rw [← finiteLaw10_map]
    apply checkIdentityNatFused_sound table finiteLaw10
    rfl
  · subst e
    rw [← finiteLaw11_map]
    apply checkIdentityNatFused_sound table finiteLaw11
    rfl
  · subst e
    rw [← finiteLaw12_map]
    apply checkIdentityNatFused_sound table finiteLaw12
    rfl
  · subst e
    rw [← finiteLaw13_map]
    apply checkIdentityNatFused_sound table finiteLaw13
    rfl
  · subst e
    rw [← finiteLaw14_map]
    apply checkIdentityNatFused_sound table finiteLaw14
    rfl
  · subst e
    rw [← finiteLaw15_map]
    apply checkIdentityNatFused_sound table finiteLaw15
    rfl
  · subst e
    rw [← finiteLaw16_map]
    apply checkIdentityNatFused_sound table finiteLaw16
    rfl
  · subst e
    rw [← finiteLaw17_map]
    apply checkIdentityNatFused_sound table finiteLaw17
    rfl
  · subst e
    rw [← finiteLaw18_map]
    apply checkIdentityNatFused_sound table finiteLaw18
    rfl
  · subst e
    rw [← finiteLaw19_map]
    apply checkIdentityNatFused_sound table finiteLaw19
    rfl
  · subst e
    rw [← finiteLaw20_map]
    apply checkIdentityNatFused_sound table finiteLaw20
    rfl
  · subst e
    rw [← finiteLaw21_map]
    apply checkIdentityNatFused_sound table finiteLaw21
    rfl
  · subst e
    rw [← finiteLaw22_map]
    apply checkIdentityNatFused_sound table finiteLaw22
    rfl
  · subst e
    rw [← finiteLaw23_map]
    apply checkIdentityNatFused_sound table finiteLaw23
    rfl
  · subst e
    rw [← finiteLaw24_map]
    apply checkIdentityNatFused_sound table finiteLaw24
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_612.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_441Family.S5_612.basisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6313
-- END S6_6313

-- BEGIN S6_6314
namespace S6_6314

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,2,4,5,2],[1,2,2,5,4,2],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "828563567923b6933e6f6a9c648096b4568c225f7df16d1c36f3fac4d06fb56e"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_613.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0, 1, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0, 1]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0, 1]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 1]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw16 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw17 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨1, [0, 1, 2, 1]⟩⟩

def targetLaw18 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def targetLaw19 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15, targetLaw16, targetLaw17, targetLaw18, targetLaw19]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

def finiteLaw7 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0, 1, 1]⟩⟩

def finiteLaw8 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0, 1]⟩⟩

def finiteLaw9 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def finiteLaw10 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0, 1]⟩⟩

def finiteLaw11 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def finiteLaw12 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw13 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 1]⟩⟩

def finiteLaw14 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw15 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw16 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw17 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨1, [0, 1, 2, 1]⟩⟩

def finiteLaw18 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩

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

theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = targetLaw9 := rfl

theorem finiteLaw10_map :
    finiteLaw10.map Fin.val = targetLaw10 := rfl

theorem finiteLaw11_map :
    finiteLaw11.map Fin.val = targetLaw11 := rfl

theorem finiteLaw12_map :
    finiteLaw12.map Fin.val = targetLaw12 := rfl

theorem finiteLaw13_map :
    finiteLaw13.map Fin.val = targetLaw13 := rfl

theorem finiteLaw14_map :
    finiteLaw14.map Fin.val = targetLaw14 := rfl

theorem finiteLaw15_map :
    finiteLaw15.map Fin.val = targetLaw15 := rfl

theorem finiteLaw16_map :
    finiteLaw16.map Fin.val = targetLaw16 := rfl

theorem finiteLaw17_map :
    finiteLaw17.map Fin.val = targetLaw17 := rfl

theorem finiteLaw18_map :
    finiteLaw18.map Fin.val = targetLaw18 := rfl

theorem finiteLaw19_map :
    finiteLaw19.map Fin.val = targetLaw19 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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
  · subst e
    rw [← finiteLaw9_map]
    apply checkIdentityNatFused_sound table finiteLaw9
    rfl
  · subst e
    rw [← finiteLaw10_map]
    apply checkIdentityNatFused_sound table finiteLaw10
    rfl
  · subst e
    rw [← finiteLaw11_map]
    apply checkIdentityNatFused_sound table finiteLaw11
    rfl
  · subst e
    rw [← finiteLaw12_map]
    apply checkIdentityNatFused_sound table finiteLaw12
    rfl
  · subst e
    rw [← finiteLaw13_map]
    apply checkIdentityNatFused_sound table finiteLaw13
    rfl
  · subst e
    rw [← finiteLaw14_map]
    apply checkIdentityNatFused_sound table finiteLaw14
    rfl
  · subst e
    rw [← finiteLaw15_map]
    apply checkIdentityNatFused_sound table finiteLaw15
    rfl
  · subst e
    rw [← finiteLaw16_map]
    apply checkIdentityNatFused_sound table finiteLaw16
    rfl
  · subst e
    rw [← finiteLaw17_map]
    apply checkIdentityNatFused_sound table finiteLaw17
    rfl
  · subst e
    rw [← finiteLaw18_map]
    apply checkIdentityNatFused_sound table finiteLaw18
    rfl
  · subst e
    rw [← finiteLaw19_map]
    apply checkIdentityNatFused_sound table finiteLaw19
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_613.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_613.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6314
-- END S6_6314

-- BEGIN S6_6315
namespace S6_6315

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,2,4,5,4],[1,2,2,5,4,5],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "cc0f852f64daa7f69690d3c5717b989c4b567d4c96f7f0b361e0722c453ce6a8"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_443Family.S5_614.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6315
-- END S6_6315

-- BEGIN S6_6316
namespace S6_6316

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,2,4,5,4],[1,2,2,5,4,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a1a2da6546c0349f1c14476d98e97d81d9182fd9ab310c1d44482c2345d4829f"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_443Family.S5_614.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6316
-- END S6_6316

-- BEGIN S6_6317
namespace S6_6317

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,3,4,4,1],[1,2,3,4,4,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8b00a62bb3001fca7f9c8bbc756079a60f8ff1eb0ba446ff19fb52133f120ed7"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
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

end S6_6317
-- END S6_6317

-- BEGIN S6_6318
namespace S6_6318

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,3,4,4,2],[1,2,3,4,4,2],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0af2648313436483bb2b915e5ae07187880a3fbb5bc8216bb9e6fd82d722f797"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (5 : Fin 6)
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

end S6_6318
-- END S6_6318

-- BEGIN S6_6321
namespace S6_6321

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,3,4,4,4],[1,2,3,4,4,5],[1,2,3,4,4,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f6914395e22bd09618acdc4eaab51038f78c4c41d478bb9899f183957e4a914a"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
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
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7]

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

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
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

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = targetLaw6 := rfl

theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = targetLaw7 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_610.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_381Family.S5_610.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6321
-- END S6_6321

-- BEGIN S6_6323
namespace S6_6323

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,3,4,5,1],[1,2,3,5,4,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "aecfd09651beb59bff69913663ed6c92e24267738ba1cf39e667fd767b4e89a0"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_612.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0, 1, 1]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0, 1]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0, 1]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 1, 0, 0]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 1]⟩⟩

def targetLaw16 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw17 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw18 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw19 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw20 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨1, [0, 1, 2, 1]⟩⟩

def targetLaw21 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩

def targetLaw22 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def targetLaw23 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [2, 0, 1, 1]⟩⟩

def targetLaw24 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15, targetLaw16, targetLaw17, targetLaw18, targetLaw19, targetLaw20, targetLaw21, targetLaw22, targetLaw23, targetLaw24]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def finiteLaw7 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

def finiteLaw8 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0, 1, 1]⟩⟩

def finiteLaw9 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0, 1]⟩⟩

def finiteLaw10 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def finiteLaw11 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0, 1]⟩⟩

def finiteLaw12 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def finiteLaw13 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 1, 0, 0]⟩⟩

def finiteLaw14 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw15 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 1]⟩⟩

def finiteLaw16 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw17 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw18 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw20 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨1, [0, 1, 2, 1]⟩⟩

def finiteLaw21 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 0, 2, 1]⟩⟩

def finiteLaw22 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def finiteLaw23 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [2, 0, 1, 1]⟩⟩

def finiteLaw24 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩

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

theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = targetLaw9 := rfl

theorem finiteLaw10_map :
    finiteLaw10.map Fin.val = targetLaw10 := rfl

theorem finiteLaw11_map :
    finiteLaw11.map Fin.val = targetLaw11 := rfl

theorem finiteLaw12_map :
    finiteLaw12.map Fin.val = targetLaw12 := rfl

theorem finiteLaw13_map :
    finiteLaw13.map Fin.val = targetLaw13 := rfl

theorem finiteLaw14_map :
    finiteLaw14.map Fin.val = targetLaw14 := rfl

theorem finiteLaw15_map :
    finiteLaw15.map Fin.val = targetLaw15 := rfl

theorem finiteLaw16_map :
    finiteLaw16.map Fin.val = targetLaw16 := rfl

theorem finiteLaw17_map :
    finiteLaw17.map Fin.val = targetLaw17 := rfl

theorem finiteLaw18_map :
    finiteLaw18.map Fin.val = targetLaw18 := rfl

theorem finiteLaw19_map :
    finiteLaw19.map Fin.val = targetLaw19 := rfl

theorem finiteLaw20_map :
    finiteLaw20.map Fin.val = targetLaw20 := rfl

theorem finiteLaw21_map :
    finiteLaw21.map Fin.val = targetLaw21 := rfl

theorem finiteLaw22_map :
    finiteLaw22.map Fin.val = targetLaw22 := rfl

theorem finiteLaw23_map :
    finiteLaw23.map Fin.val = targetLaw23 := rfl

theorem finiteLaw24_map :
    finiteLaw24.map Fin.val = targetLaw24 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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
  · subst e
    rw [← finiteLaw9_map]
    apply checkIdentityNatFused_sound table finiteLaw9
    rfl
  · subst e
    rw [← finiteLaw10_map]
    apply checkIdentityNatFused_sound table finiteLaw10
    rfl
  · subst e
    rw [← finiteLaw11_map]
    apply checkIdentityNatFused_sound table finiteLaw11
    rfl
  · subst e
    rw [← finiteLaw12_map]
    apply checkIdentityNatFused_sound table finiteLaw12
    rfl
  · subst e
    rw [← finiteLaw13_map]
    apply checkIdentityNatFused_sound table finiteLaw13
    rfl
  · subst e
    rw [← finiteLaw14_map]
    apply checkIdentityNatFused_sound table finiteLaw14
    rfl
  · subst e
    rw [← finiteLaw15_map]
    apply checkIdentityNatFused_sound table finiteLaw15
    rfl
  · subst e
    rw [← finiteLaw16_map]
    apply checkIdentityNatFused_sound table finiteLaw16
    rfl
  · subst e
    rw [← finiteLaw17_map]
    apply checkIdentityNatFused_sound table finiteLaw17
    rfl
  · subst e
    rw [← finiteLaw18_map]
    apply checkIdentityNatFused_sound table finiteLaw18
    rfl
  · subst e
    rw [← finiteLaw19_map]
    apply checkIdentityNatFused_sound table finiteLaw19
    rfl
  · subst e
    rw [← finiteLaw20_map]
    apply checkIdentityNatFused_sound table finiteLaw20
    rfl
  · subst e
    rw [← finiteLaw21_map]
    apply checkIdentityNatFused_sound table finiteLaw21
    rfl
  · subst e
    rw [← finiteLaw22_map]
    apply checkIdentityNatFused_sound table finiteLaw22
    rfl
  · subst e
    rw [← finiteLaw23_map]
    apply checkIdentityNatFused_sound table finiteLaw23
    rfl
  · subst e
    rw [← finiteLaw24_map]
    apply checkIdentityNatFused_sound table finiteLaw24
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_612.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_441Family.S5_612.basisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6323
-- END S6_6323

-- BEGIN S6_6324
namespace S6_6324

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,3,4,5,2],[1,2,3,5,4,2],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "df1fe465c612e5ddad6ac516b73c42eba51b3336ad33c385f95e47bf28fffabc"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_613.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0, 1, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0, 1]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0, 1]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 1]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw16 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw17 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨1, [0, 1, 2, 1]⟩⟩

def targetLaw18 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def targetLaw19 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15, targetLaw16, targetLaw17, targetLaw18, targetLaw19]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1, 1]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 1, 0]⟩⟩

def finiteLaw7 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0, 1, 1]⟩⟩

def finiteLaw8 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0, 1]⟩⟩

def finiteLaw9 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def finiteLaw10 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0, 1]⟩⟩

def finiteLaw11 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def finiteLaw12 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw13 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨1, [0, 1, 1]⟩⟩

def finiteLaw14 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw15 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw16 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw17 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 0]⟩, ⟨1, [0, 1, 2, 1]⟩⟩

def finiteLaw18 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 1]⟩, ⟨1, [0, 0, 2, 1]⟩⟩

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

theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = targetLaw9 := rfl

theorem finiteLaw10_map :
    finiteLaw10.map Fin.val = targetLaw10 := rfl

theorem finiteLaw11_map :
    finiteLaw11.map Fin.val = targetLaw11 := rfl

theorem finiteLaw12_map :
    finiteLaw12.map Fin.val = targetLaw12 := rfl

theorem finiteLaw13_map :
    finiteLaw13.map Fin.val = targetLaw13 := rfl

theorem finiteLaw14_map :
    finiteLaw14.map Fin.val = targetLaw14 := rfl

theorem finiteLaw15_map :
    finiteLaw15.map Fin.val = targetLaw15 := rfl

theorem finiteLaw16_map :
    finiteLaw16.map Fin.val = targetLaw16 := rfl

theorem finiteLaw17_map :
    finiteLaw17.map Fin.val = targetLaw17 := rfl

theorem finiteLaw18_map :
    finiteLaw18.map Fin.val = targetLaw18 := rfl

theorem finiteLaw19_map :
    finiteLaw19.map Fin.val = targetLaw19 := rfl

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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
  · subst e
    rw [← finiteLaw9_map]
    apply checkIdentityNatFused_sound table finiteLaw9
    rfl
  · subst e
    rw [← finiteLaw10_map]
    apply checkIdentityNatFused_sound table finiteLaw10
    rfl
  · subst e
    rw [← finiteLaw11_map]
    apply checkIdentityNatFused_sound table finiteLaw11
    rfl
  · subst e
    rw [← finiteLaw12_map]
    apply checkIdentityNatFused_sound table finiteLaw12
    rfl
  · subst e
    rw [← finiteLaw13_map]
    apply checkIdentityNatFused_sound table finiteLaw13
    rfl
  · subst e
    rw [← finiteLaw14_map]
    apply checkIdentityNatFused_sound table finiteLaw14
    rfl
  · subst e
    rw [← finiteLaw15_map]
    apply checkIdentityNatFused_sound table finiteLaw15
    rfl
  · subst e
    rw [← finiteLaw16_map]
    apply checkIdentityNatFused_sound table finiteLaw16
    rfl
  · subst e
    rw [← finiteLaw17_map]
    apply checkIdentityNatFused_sound table finiteLaw17
    rfl
  · subst e
    rw [← finiteLaw18_map]
    apply checkIdentityNatFused_sound table finiteLaw18
    rfl
  · subst e
    rw [← finiteLaw19_map]
    apply checkIdentityNatFused_sound table finiteLaw19
    rfl

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_613.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_613.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6324
-- END S6_6324

-- BEGIN S6_6325
namespace S6_6325

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[1,2,3,4,5,4],[1,2,3,5,4,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "41fa365d30ae58404ecf921518ec7e44e509b15448b558521f0c6152988314e3"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_614.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_443Family.S5_614.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6325
-- END S6_6325

-- BEGIN S6_6328
namespace S6_6328

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5f33cd62694d1a8acd443fb4de96a5884754b65d2469273b5ca26fa64f8d37a1"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_592.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (1 : Fin 6) else (5 : Fin 6)
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_592.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_343Family.S5_592.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6328
-- END S6_6328

-- BEGIN S6_6331
namespace S6_6331

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,1,1,1,1,2],[4,4,4,4,4,4],[4,4,4,4,4,4],[1,2,2,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "77bc742d32d6519c52a331dd521e0afd67c9a8332489b0b83441c040232b2a74"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_593.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (1 : Fin 6) else (5 : Fin 6)
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
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7]

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
  ⟨⟨0, [0, 1, 2, 1]⟩, ⟨0, [1, 1, 2, 0]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_593.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_345Family.S5_593.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_6331
-- END S6_6331

end SemigroupBasis.Generated.Order6FinalL5TransferV3

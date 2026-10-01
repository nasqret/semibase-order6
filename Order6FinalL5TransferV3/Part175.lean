import SemigroupBasis.CoRoots.S5_342Family
import SemigroupBasis.CoRoots.S5_344Family
import SemigroupBasis.CoRoots.S5_348Family
import SemigroupBasis.CoRoots.S5_787Family
import SemigroupBasis.CoRoots.S5_790Family
import SemigroupBasis.CoRoots.S5_803
import SemigroupBasis.CoRoots.S5_804Completeness
import SemigroupBasis.CoRoots.S5_806Completeness
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_69
import SemigroupBasis.Generated.S4_70
import SemigroupBasis.Generated.S5_400PublishedRoots
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

-- BEGIN S6_7563
namespace S6_7563

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,1,4,4,4],[1,1,1,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3fea3542165e5c8991565b295d5a2700713858f32de3a377a15e86666a74fada"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_348.table.semigroup table.semigroup where
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
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6]

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
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_348.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_348Family.S5_348.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7563
-- END S6_7563

-- BEGIN S6_7568
namespace S6_7568

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,1,4,4,4],[1,2,1,4,5,5],[1,2,1,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "27072a2aec63a324288a1979cb6dff36f0e51842e08cf17071fca66452a620ac"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_353.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_342Family.S5_353.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7568
-- END S6_7568

-- BEGIN S6_7569
namespace S6_7569

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,1,4,4,4],[1,2,1,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "2350a8860268c9861963a21f85ee3ae7ec27a7d52a9a06df2f617f9329bea253"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_354.table.semigroup table.semigroup where
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
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6]

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
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_354.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_348Family.S5_354.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7569
-- END S6_7569

-- BEGIN S6_7571
namespace S6_7571

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,1,4,4,4],[1,2,3,4,5,5],[1,2,3,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0d75908a7a74a7f307a59e6c19cb6e148ee0ab27256442002d1a20a9121a6843"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_356.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_344Family.S5_356.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7571
-- END S6_7571

-- BEGIN S6_7573
namespace S6_7573

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,1,1],[1,1,1,1,5,5],[1,2,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "619c3503cffcde186b6b5196b01f9114da4bba107e6bf03f877b50c48a15cf0e"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_7573
-- END S6_7573

-- BEGIN S6_7574
namespace S6_7574

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,1,1],[1,2,1,1,5,5],[1,2,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0702251ea91c0556bd80e9b0889b71d4c35dcbf719bdbc81a884cbb7c6104f39"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_7574
-- END S6_7574

-- BEGIN S6_7575
namespace S6_7575

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,1,1],[1,2,1,1,5,5],[1,2,1,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "60dcdd5ddf12aab8879da5393e090ed71a9828fa6efd3f0eda4d95122e55a2f2"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_803.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (3 : Fin 6)
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
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨2, [0, 1, 0]⟩, ⟨2, [1, 0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨2, [0, 1, 0]⟩, ⟨2, [1, 0, 1]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_803.table.semigroup.opposite targetBasis := by
  exact SemigroupBasis.CoRoots.S5_803.representative_basis.oppositeReversed

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7575
-- END S6_7575

-- BEGIN S6_7576
namespace S6_7576

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,1,1],[1,2,1,1,5,6],[1,2,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ea60f420774aeb33e7141828774ab74f6fb6ba5c032f8c1075be933504d9885b"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨1, [2, 1, 0]⟩, ⟨2, [1, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨1, [2, 1, 0]⟩, ⟨2, [1, 2, 0]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup.opposite targetBasis := by
  exact SemigroupBasis.CoRoots.S5_787Family.S5_796.basis_complete.oppositeReversed

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7576
-- END S6_7576

-- BEGIN S6_7577
namespace S6_7577

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,1,3],[1,2,1,1,5,5],[1,2,1,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3c0d7ea1a4e24b14c5dc3a05fe0ee3cf4b568c013b4279ef60f0b53ecbd28c7f"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 1, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 1, 0]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 0, 1]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup.opposite targetBasis := by
  exact SemigroupBasis.CoRoots.S5_804.basisFor.oppositeReversed

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7577
-- END S6_7577

-- BEGIN S6_7578
namespace S6_7578

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,1,4],[1,1,1,1,5,5],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "3697ba9db559ec9878fdde6c844dacdcdf48e47825aca842aba0c649445b7d8c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 2, 3, 2]⟩, ⟨0, [2, 0, 3, 2]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [0, 2, 2]⟩, ⟨0, [2, 0, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 4) :=
  ⟨⟨0, [0, 2, 3, 2]⟩, ⟨0, [2, 0, 3, 2]⟩⟩

def finiteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 2]⟩, ⟨0, [2, 0, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw7 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def finiteLaw10 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def finiteLaw11 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def finiteLaw12 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def finiteLaw13 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def finiteLaw14 : Identity (Fin 4) :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def finiteLaw15 : Identity (Fin 3) :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup targetBasis := by
  exact SemigroupBasis.Generated.S5_400PublishedRoots.S5_840.representativeBasisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_7578
-- END S6_7578

-- BEGIN S6_7579
namespace S6_7579

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,1,4],[1,1,1,1,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d85dee4e33c044a8ccb02cc02b687f4b1969d79a0cb5d6b82cc3cf26f218535f"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 2, 3, 2]⟩, ⟨0, [2, 0, 3, 2]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [0, 2, 2]⟩, ⟨0, [2, 0, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 4) :=
  ⟨⟨0, [0, 2, 3, 2]⟩, ⟨0, [2, 0, 3, 2]⟩⟩

def finiteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 2]⟩, ⟨0, [2, 0, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw7 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def finiteLaw10 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def finiteLaw11 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def finiteLaw12 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def finiteLaw13 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def finiteLaw14 : Identity (Fin 4) :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def finiteLaw15 : Identity (Fin 3) :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup targetBasis := by
  exact SemigroupBasis.Generated.S5_400PublishedRoots.S5_840.representativeBasisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7579
-- END S6_7579

-- BEGIN S6_7580
namespace S6_7580

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,1,4],[1,2,1,1,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e69b83b44a623a8e4a138a318cca23002e84cd072077ed3143ca7f0dabaf2621"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 2, 3, 2]⟩, ⟨0, [2, 0, 3, 2]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [0, 2, 2]⟩, ⟨0, [2, 0, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 4) :=
  ⟨⟨0, [0, 2, 3, 2]⟩, ⟨0, [2, 0, 3, 2]⟩⟩

def finiteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 2]⟩, ⟨0, [2, 0, 2]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def finiteLaw6 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw7 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def finiteLaw10 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def finiteLaw11 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def finiteLaw12 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def finiteLaw13 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def finiteLaw14 : Identity (Fin 4) :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def finiteLaw15 : Identity (Fin 3) :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup targetBasis := by
  exact SemigroupBasis.Generated.S5_400PublishedRoots.S5_840.representativeBasisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7580
-- END S6_7580

-- BEGIN S6_7581
namespace S6_7581

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,3,3],[1,1,1,1,5,5],[1,2,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "015d46cda748db88f85a6dbcc598834db0a5308884e772f84b7cab06c6e69c4f"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_7581
-- END S6_7581

-- BEGIN S6_7582
namespace S6_7582

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,3,3],[1,2,1,1,5,5],[1,2,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "67bc956c3580b4e7d432a58549ce477cefd8bbe5d69a61f84c4fa8abe0f3d5fb"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
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

end S6_7582
-- END S6_7582

-- BEGIN S6_7583
namespace S6_7583

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,3,3],[1,2,1,1,5,5],[1,2,1,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "47af1d2afd9e8f965fbd96628eb6ca7e7dd254d274c1fb5242a0cd35f1edd479"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 1, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨2, [0, 1, 0]⟩, ⟨2, [1, 0, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 1, 0]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨2, [0, 1, 0]⟩, ⟨2, [1, 0, 1]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite targetBasis := by
  exact SemigroupBasis.CoRoots.S5_806.basisFor.oppositeReversed

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7583
-- END S6_7583

-- BEGIN S6_7584
namespace S6_7584

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,3,3],[1,1,3,4,3,3],[1,2,1,1,5,6],[1,2,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "55c5ef0a1119b5e2a9879adbd2cf8548bf5069439894685b6543baccac8eb224"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (3 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨1, [2, 1, 0]⟩, ⟨2, [1, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨1, [2, 1, 0]⟩, ⟨2, [1, 2, 0]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup.opposite targetBasis := by
  exact SemigroupBasis.CoRoots.S5_790Family.S5_798.basis_complete.oppositeReversed

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_7584
-- END S6_7584

end SemigroupBasis.Generated.Order6FinalL5TransferV3

import SemigroupBasis.CoRoots.S5_787Family
import SemigroupBasis.CoRoots.S5_788Family
import SemigroupBasis.CoRoots.S5_793Family
import SemigroupBasis.CoRoots.S5_855
import SemigroupBasis.CoRoots.S5_860Family
import SemigroupBasis.CoRoots.S5_863Family
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S5_400PublishedRoots
import SemigroupBasis.Generated.S5_808Transfers
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

-- BEGIN S6_13266
namespace S6_13266

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,3,1,3,3],[4,4,4,4,4,4],[1,1,3,4,5,6],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "32cc4c1f1505a645c54d998f76371dd062ddbf1a118d4b61049e7b20ad05fadb"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_855.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_855.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_855.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13266
-- END S6_13266

-- BEGIN S6_13270
namespace S6_13270

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,3,1,3,3],[4,4,4,4,4,4],[1,2,3,1,5,6],[1,2,3,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "31f76d124a6bdea47eb015167654f7ea9e7221f62b0c9f51c0db5ed4ad370d9d"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_860.table.semigroup table.semigroup where
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
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 3]⟩, ⟨0, [2, 1, 3]⟩⟩

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

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def finiteLaw7 : Identity (Fin 4) :=
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_860.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_860Family.S5_860.basisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13270
-- END S6_13270

-- BEGIN S6_13273
namespace S6_13273

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,3,1,3,3],[4,4,4,4,4,4],[1,2,3,4,5,6],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6827ed747ba25ab505912264e3e08408a527a235fac1165db941ffa7fd70b140"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_863.table.semigroup table.semigroup where
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
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_863.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_863Family.S5_863.basisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13273
-- END S6_13273

-- BEGIN S6_13296
namespace S6_13296

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,3,3,3,3],[1,2,3,4,3,4],[1,1,3,3,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0dee16c699d307ebc045add5ad0869a3c39a5eaef2d988067d923ecda143168e"

def subMul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def subTable : FiniteTable where
  order := 6
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup table.semigroup where
  toFun := fun a : Fin 6 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  toFun := fun a : Fin 6 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (4 : Fin 6) else (5 : Fin 6)
  right_inverse := by
    intro b
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
  acceptedSourceBasis.inheritAlongSubsemigroupQuotient subEmbedding quotient targetModels

end S6_13296
-- END S6_13296

-- BEGIN S6_13298
namespace S6_13298

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,3,3,3,3],[1,2,3,4,4,4],[1,2,3,4,5,5],[1,2,3,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "d793fb17a26dec76d35196bc9913601f9babaade56acf110b98a9f87b3b6d365"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_843.table.semigroup table.semigroup where
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
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

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
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 0]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_843.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_793Family.S5_843.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13298
-- END S6_13298

-- BEGIN S6_13299
namespace S6_13299

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,3,3,3,3],[1,2,3,4,4,4],[1,2,3,4,5,6],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "35ae15493e19bcfced4b55fb3316092d089c1c4c31b389352f2627b59e0b0d98"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 1, 2]⟩, ⟨0, [1, 1, 0, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_844.table.semigroup targetBasis := by
  exact SemigroupBasis.Generated.S5_808Transfers.S5_844.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13299
-- END S6_13299

-- BEGIN S6_13314
namespace S6_13314

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,3,4,3,3],[4,4,4,4,4,4],[1,1,3,4,5,6],[1,1,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "268e28080805d5329b1e2be824ae6d1de9e31acfa85d955727baff3575db6ce2"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_855.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_855.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_855.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13314
-- END S6_13314

-- BEGIN S6_13317
namespace S6_13317

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,1,3,4,3,3],[4,4,4,4,4,4],[1,2,3,4,5,6],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "bd03cf7e7037921df4c2fcc9ee92a21601198be477175533492f5fc6a5901bbf"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_863.table.semigroup table.semigroup where
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
  ⟨⟨0, [0, 1, 2]⟩, ⟨0, [1, 0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨0, [1, 0, 1]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_863.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_863Family.S5_863.basisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13317
-- END S6_13317

-- BEGIN S6_13323
namespace S6_13323

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,1],[4,4,4,4,4,4],[1,1,1,1,5,5],[1,1,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4f087638828c0f34563e3564864daefee0cee3b5287921e4c555a91fd188e0cc"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)
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
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_787Family.S5_787.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13323
-- END S6_13323

-- BEGIN S6_13324
namespace S6_13324

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,1],[4,4,4,4,4,4],[1,1,1,1,5,5],[1,1,1,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b2933a3e291e508aab1680c14d297f75f072279d7d7505d97d3294fead0cd762"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)
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
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_787Family.S5_787.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13324
-- END S6_13324

-- BEGIN S6_13325
namespace S6_13325

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,1],[4,4,4,4,4,4],[1,1,1,1,5,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b840ed948152d84ced849518125d944275ddc88554a159557bb90076d74ba3f7"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)
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
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 0, 1, 1, 0, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1, 1, 2]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 2]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 1]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 1, 2, 0]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 2, 1, 0]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 1, 0, 2]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 0, 1]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 1, 0]⟩⟩

def targetLaw16 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 1, 0, 2, 2, 0]⟩⟩

def targetLaw17 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 1, 2, 0]⟩⟩

def targetLaw18 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 0, 2]⟩⟩

def targetLaw19 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 2, 0]⟩⟩

def targetLaw20 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 0, 1]⟩⟩

def targetLaw21 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def targetLaw22 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 2, 0]⟩⟩

def targetLaw23 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 1, 2, 2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15, targetLaw16, targetLaw17, targetLaw18, targetLaw19, targetLaw20, targetLaw21, targetLaw22, targetLaw23]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 0, 1, 1, 0, 2]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1, 1, 2]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 1]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 2]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 0]⟩⟩

def finiteLaw10 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 1]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 1, 2, 0]⟩⟩

def finiteLaw12 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 2, 1, 0]⟩⟩

def finiteLaw13 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 1, 0, 2]⟩⟩

def finiteLaw14 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 0, 1]⟩⟩

def finiteLaw15 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 1, 0]⟩⟩

def finiteLaw16 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 1, 0, 2, 2, 0]⟩⟩

def finiteLaw17 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 1, 2, 0]⟩⟩

def finiteLaw18 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 0, 2]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 2, 0]⟩⟩

def finiteLaw20 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 0, 1]⟩⟩

def finiteLaw21 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def finiteLaw22 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 2, 0]⟩⟩

def finiteLaw23 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 1, 2, 2, 1]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_788Family.S5_788.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13325
-- END S6_13325

-- BEGIN S6_13326
namespace S6_13326

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,1],[4,4,4,4,4,4],[1,1,1,1,5,5],[4,4,4,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1a7c5cd28946d9fc8d5e3b26d4befd23e012d59f2fe5982286389348e569f8be"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)
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
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_787.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_787Family.S5_787.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13326
-- END S6_13326

-- BEGIN S6_13328
namespace S6_13328

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,1],[4,4,4,4,4,4],[1,1,1,4,5,5],[1,1,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ff2ca8a9096037acc9429e4d865e6215af93a5804973f2fdb3131548f260fd16"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)
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
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 0, 1, 1, 0, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1, 1, 2]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 2]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 1]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 1, 2, 0]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 2, 1, 0]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 1, 0, 2]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 0, 1]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 1, 0]⟩⟩

def targetLaw16 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 1, 0, 2, 2, 0]⟩⟩

def targetLaw17 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 1, 2, 0]⟩⟩

def targetLaw18 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 0, 2]⟩⟩

def targetLaw19 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 2, 0]⟩⟩

def targetLaw20 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 0, 1]⟩⟩

def targetLaw21 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def targetLaw22 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 2, 0]⟩⟩

def targetLaw23 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 1, 2, 2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15, targetLaw16, targetLaw17, targetLaw18, targetLaw19, targetLaw20, targetLaw21, targetLaw22, targetLaw23]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 0, 1, 1, 0, 2]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1, 1, 2]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 1]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 2]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 0]⟩⟩

def finiteLaw10 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 1]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 1, 2, 0]⟩⟩

def finiteLaw12 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 2, 1, 0]⟩⟩

def finiteLaw13 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 1, 0, 2]⟩⟩

def finiteLaw14 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 0, 1]⟩⟩

def finiteLaw15 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 1, 0]⟩⟩

def finiteLaw16 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 1, 0, 2, 2, 0]⟩⟩

def finiteLaw17 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 1, 2, 0]⟩⟩

def finiteLaw18 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 0, 2]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 2, 0]⟩⟩

def finiteLaw20 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 0, 1]⟩⟩

def finiteLaw21 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def finiteLaw22 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 2, 0]⟩⟩

def finiteLaw23 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 1, 2, 2, 1]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_788Family.S5_788.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13328
-- END S6_13328

-- BEGIN S6_13329
namespace S6_13329

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,1],[4,4,4,4,4,4],[1,1,1,4,5,5],[1,1,1,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ce707ceb76bb0015fd4dd59dbadcddb79f81392b8964d0e7520cb03c48b8c226"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)
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
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 0, 1, 1, 0, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1, 1, 2]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 2]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 1]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 1, 2, 0]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 2, 1, 0]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 1, 0, 2]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 0, 1]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 1, 0]⟩⟩

def targetLaw16 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 1, 0, 2, 2, 0]⟩⟩

def targetLaw17 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 1, 2, 0]⟩⟩

def targetLaw18 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 0, 2]⟩⟩

def targetLaw19 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 2, 0]⟩⟩

def targetLaw20 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 0, 1]⟩⟩

def targetLaw21 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def targetLaw22 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 2, 0]⟩⟩

def targetLaw23 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 1, 2, 2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15, targetLaw16, targetLaw17, targetLaw18, targetLaw19, targetLaw20, targetLaw21, targetLaw22, targetLaw23]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 0, 1, 1, 0, 2]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1, 1, 2]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 1]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 2]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 0]⟩⟩

def finiteLaw10 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 1]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 1, 2, 0]⟩⟩

def finiteLaw12 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 2, 1, 0]⟩⟩

def finiteLaw13 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 1, 0, 2]⟩⟩

def finiteLaw14 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 0, 1]⟩⟩

def finiteLaw15 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 1, 0]⟩⟩

def finiteLaw16 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 1, 0, 2, 2, 0]⟩⟩

def finiteLaw17 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 1, 2, 0]⟩⟩

def finiteLaw18 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 0, 2]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 2, 0]⟩⟩

def finiteLaw20 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 0, 1]⟩⟩

def finiteLaw21 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def finiteLaw22 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 2, 0]⟩⟩

def finiteLaw23 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 1, 2, 2, 1]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_788Family.S5_788.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13329
-- END S6_13329

-- BEGIN S6_13331
namespace S6_13331

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,1],[4,4,4,4,4,4],[1,1,1,4,5,6],[4,4,4,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b6d632317630806d1874b6a25733d4eb12c787c3bacd1f7ec8905053e0a3a3f3"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)
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
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 0, 1, 1, 0, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1, 1, 2]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 2]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 1]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 1, 2, 0]⟩⟩

def targetLaw12 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 2, 1, 0]⟩⟩

def targetLaw13 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 1, 0, 2]⟩⟩

def targetLaw14 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 0, 1]⟩⟩

def targetLaw15 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 1, 0]⟩⟩

def targetLaw16 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 1, 0, 2, 2, 0]⟩⟩

def targetLaw17 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 1, 2, 0]⟩⟩

def targetLaw18 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 0, 2]⟩⟩

def targetLaw19 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 2, 0]⟩⟩

def targetLaw20 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 0, 1]⟩⟩

def targetLaw21 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def targetLaw22 : Identity Nat :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 2, 0]⟩⟩

def targetLaw23 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 1, 2, 2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11, targetLaw12, targetLaw13, targetLaw14, targetLaw15, targetLaw16, targetLaw17, targetLaw18, targetLaw19, targetLaw20, targetLaw21, targetLaw22, targetLaw23]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [1, 0, 1, 1, 0, 2]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 0]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 2]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [0, 1, 2, 1, 1, 2]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 1]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 0, 1, 2, 2]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 0]⟩⟩

def finiteLaw10 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 0, 2, 1]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 1, 2, 0]⟩⟩

def finiteLaw12 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 1, 2, 1, 0]⟩⟩

def finiteLaw13 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 1, 0, 2]⟩⟩

def finiteLaw14 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 0, 1]⟩⟩

def finiteLaw15 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 0, 2, 2, 1, 0]⟩⟩

def finiteLaw16 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 1, 0, 2, 2, 0]⟩⟩

def finiteLaw17 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 0, 1, 2, 0]⟩⟩

def finiteLaw18 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 0, 2]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 1, 2, 0]⟩⟩

def finiteLaw20 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 0, 1]⟩⟩

def finiteLaw21 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def finiteLaw22 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [1, 2, 1, 2, 2, 0]⟩⟩

def finiteLaw23 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [1, 2, 1, 2, 2, 1]⟩⟩

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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_788Family.S5_788.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13331
-- END S6_13331

-- BEGIN S6_13332
namespace S6_13332

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,1,1],[4,4,4,4,4,4],[4,4,4,4,5,5],[4,4,4,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "b24e0ba90ad9fbf2d1713899a92739eb5e09785f33591712b4f37e9280133942"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_789.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)
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
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 1]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0]⟩, ⟨0, [2, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_789.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_787Family.S5_789.basis_complete

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_13332
-- END S6_13332

end SemigroupBasis.Generated.Order6FinalL5TransferV3

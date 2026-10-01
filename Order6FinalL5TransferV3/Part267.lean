import SemigroupBasis.CoRoots.S5_787Family
import SemigroupBasis.CoRoots.S5_790Family
import SemigroupBasis.CoRoots.S5_793Family
import SemigroupBasis.CoRoots.S5_803
import SemigroupBasis.CoRoots.S5_804Completeness
import SemigroupBasis.CoRoots.S5_806Completeness
import SemigroupBasis.CoRoots.S5_841Completeness
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

-- BEGIN S6_11194
namespace S6_11194

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,1],[1,2,3,3,1,1],[1,1,1,1,5,5],[1,1,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "024e908e1bab73ee05cb624c12168b697cfaaae5ad586337de3fce4a53cb5064"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_69.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
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

end S6_11194
-- END S6_11194

-- BEGIN S6_11195
namespace S6_11195

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,1],[1,2,3,3,1,1],[1,1,1,1,5,5],[1,1,1,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "20139c6db9b8bf8a88a2895f62952939de10d27e499cc2831be84133c3067641"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_803.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (2 : Fin 6)
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

end S6_11195
-- END S6_11195

-- BEGIN S6_11196
namespace S6_11196

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,1],[1,2,3,3,1,1],[1,1,1,1,5,6],[1,1,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5608255e46bbe660ddb00454b12daab94d1dcf771c66edd8d9471308c9631b15"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (2 : Fin 6)
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

end S6_11196
-- END S6_11196

-- BEGIN S6_11197
namespace S6_11197

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,2],[1,2,3,3,1,2],[1,1,1,1,5,5],[1,1,1,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8e2355c258dfbf6129c5e27000d562506303af8f2e466750dc5d3e91b2a1565d"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (2 : Fin 6)
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

end S6_11197
-- END S6_11197

-- BEGIN S6_11198
namespace S6_11198

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,3],[1,2,3,3,1,3],[1,1,1,1,5,5],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "0653cb9f0ca652d2bab7c49dee51edb40c6f41206144fc333e191b5d0710e7ac"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
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

end S6_11198
-- END S6_11198

-- BEGIN S6_11199
namespace S6_11199

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,3],[1,2,3,3,1,3],[1,1,1,1,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "ec18d7805084ee9bd3598e07a58d53bf6ed94dd7079e327b5a86c32fe33d98ca"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
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

end S6_11199
-- END S6_11199

-- BEGIN S6_11200
namespace S6_11200

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,3],[1,2,3,3,1,4],[1,1,1,1,5,5],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "f223b99839297cd39d63671879de2e5ee222e7d98d097d247d6aae2e278cac0e"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
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

end S6_11200
-- END S6_11200

-- BEGIN S6_11201
namespace S6_11201

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,1,3],[1,2,3,3,1,4],[1,1,1,1,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "63598721906c341064529f1c65798fd74774eb982cc03870ddb3c2141f9403c6"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
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

end S6_11201
-- END S6_11201

-- BEGIN S6_11202
namespace S6_11202

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,2,2],[1,2,3,3,2,2],[1,1,1,1,5,5],[1,1,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9286fae0ad7322e4a6adf4ca6c6f9ccd77b84040cec40b7de1cd69e68dd8a8ed"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_70.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
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

end S6_11202
-- END S6_11202

-- BEGIN S6_11203
namespace S6_11203

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,2,2],[1,2,3,3,2,2],[1,1,1,1,5,5],[1,1,1,1,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8de04c4e03c59a7099d809a69542f1febd264af7f6a57d89a3ed471cf6d77ce3"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_806.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (2 : Fin 6)
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

end S6_11203
-- END S6_11203

-- BEGIN S6_11204
namespace S6_11204

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,2,2],[1,2,3,3,2,2],[1,1,1,1,5,6],[1,1,1,1,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "8d0991ac2da4549a1aa93d5d54e504603fdd949620becabb81b6a2aaba10006a"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup.opposite table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (2 : Fin 6)
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

end S6_11204
-- END S6_11204

-- BEGIN S6_11205
namespace S6_11205

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,2,3],[1,2,3,3,2,3],[1,1,1,1,5,5],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "961265c8aef6739690989adb781644b5dcd5af3b6c55d7ab23cc3a2b872a844e"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw6 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def finiteLaw7 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def finiteLaw10 : Identity (Fin 4) :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_841.catalogueS5_841BasisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_11205
-- END S6_11205

-- BEGIN S6_11206
namespace S6_11206

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,2,3],[1,2,3,3,2,3],[1,1,1,1,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e90ba1f6fc7ab7af8789472b505d2b29dc61fd11f7ca39b61d122a70f795fec9"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw6 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def finiteLaw7 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def finiteLaw10 : Identity (Fin 4) :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_841.catalogueS5_841BasisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_11206
-- END S6_11206

-- BEGIN S6_11207
namespace S6_11207

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,2,3],[1,2,3,3,2,4],[1,1,1,1,5,5],[1,2,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "1f23aa58c942fcf4a4f7a29f1893375c1903c80838a83957c296771da96957ea"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw6 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def finiteLaw7 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def finiteLaw10 : Identity (Fin 4) :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_841.catalogueS5_841BasisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_11207
-- END S6_11207

-- BEGIN S6_11208
namespace S6_11208

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,2,3],[1,2,3,3,2,4],[1,1,1,1,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "86aaffde46f0a5ff5a6ec7a974519b286756050de40f315f5121376e8e174407"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def targetLaw5 : Identity Nat :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def targetLaw6 : Identity Nat :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def targetLaw7 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def targetLaw8 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def targetLaw9 : Identity Nat :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def targetLaw10 : Identity Nat :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def targetLaw11 : Identity Nat :=
  ⟨⟨0, [2, 0, 2]⟩, ⟨0, [2, 2, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4, targetLaw5, targetLaw6, targetLaw7, targetLaw8, targetLaw9, targetLaw10, targetLaw11]

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0, 2, 0]⟩, ⟨0, [2, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 4) :=
  ⟨⟨0, [1, 0, 3, 1]⟩, ⟨1, [0, 0, 3, 1]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0, 1]⟩, ⟨1, [0, 0, 1]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2, 0]⟩, ⟨0, [1, 2, 0]⟩⟩

def finiteLaw6 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩

def finiteLaw7 : Identity (Fin 4) :=
  ⟨⟨0, [1, 2, 0, 3, 1]⟩, ⟨1, [0, 2, 0, 3, 1]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 1]⟩, ⟨1, [0, 2, 0, 1]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 0, 2]⟩, ⟨0, [1, 2, 2, 0]⟩⟩

def finiteLaw10 : Identity (Fin 4) :=
  ⟨⟨0, [2, 3, 0, 2]⟩, ⟨0, [2, 3, 2, 0]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
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

theorem targetModels :
    Models table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he
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

theorem acceptedSourceBasis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_841.table.semigroup targetBasis := by
  exact SemigroupBasis.CoRoots.S5_841.catalogueS5_841BasisFor

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_11208
-- END S6_11208

-- BEGIN S6_11210
namespace S6_11210

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,3,3,3],[1,2,3,3,3,3],[1,2,3,3,5,5],[1,2,3,3,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "975460c7ba22f76ee2a7ec46c600855c25413fdb76549e2484f2cc5531c90a76"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_843.table.semigroup table.semigroup where
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

end S6_11210
-- END S6_11210

end SemigroupBasis.Generated.Order6FinalL5TransferV3

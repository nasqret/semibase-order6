import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_2
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

-- BEGIN S6_18
namespace S6_18

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,1,3,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5f4e3f1e47e3753dfa5424140a9f06dae4ea016fae4279f6ff9739968fcdb38a"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_18
-- END S6_18

-- BEGIN S6_19
namespace S6_19

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,2,1,1,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e092dcf1b8fd11794f611f53fbf50e7f56a3bbbd8d350eb8048a94df23354469"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_19
-- END S6_19

-- BEGIN S6_20
namespace S6_20

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,2,1,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "c8bab0a6ed1ef383163f9950be8f86ce2257e1f29be8032b5a0a2700265d8131"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_20
-- END S6_20

-- BEGIN S6_21
namespace S6_21

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,2,2,1,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "945a84b42dcdf601e68e8aaad651e4de53bad1d05f974c506e191a921706712c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_21
-- END S6_21

-- BEGIN S6_22
namespace S6_22

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,2,2,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "33278e0b6a2e8442eb673b3c32ccfc79fe0748c36404a756575704bbb7b4783c"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_22
-- END S6_22

-- BEGIN S6_23
namespace S6_23

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,1,2,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "34ac33ce048725abfb0dce2a19f8b99d83f191e764a6e66d0d269d6ed8237d72"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_23
-- END S6_23

-- BEGIN S6_24
namespace S6_24

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,1,2,3,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e28c1c573f82c606b5e5106aa36ee0258ea0ce14dd097d128b8814b4c2101f31"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_24
-- END S6_24

-- BEGIN S6_25
namespace S6_25

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,1,3,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "73fc9529dcb262b03b37b46b572402f531e98bbc2528a242b16206d0eb21cd40"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_25
-- END S6_25

-- BEGIN S6_26
namespace S6_26

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,1,3,3,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "5c46052c095f49fab030f59107f0eaf1f5012403e7f04dffd6890cf1efbcfea4"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_26
-- END S6_26

-- BEGIN S6_27
namespace S6_27

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,2,1,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "e6d7f178df709925d9ea6e6594c0b393c1c172ca18c77a1ad23bed0e8dd3c1b2"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_27
-- END S6_27

-- BEGIN S6_28
namespace S6_28

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,2,2,1,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "acb782e35f58a55d4700fef7a74b84640f69a3010b2ab02822be5919a48d407a"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_28
-- END S6_28

-- BEGIN S6_29
namespace S6_29

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,2],[1,1,2,2,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "6ed97313d6218ec6d8f68f1fbf71ed03273529a45b26d49feab9066a88ece8c2"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (5 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_29
-- END S6_29

-- BEGIN S6_30
namespace S6_30

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,3],[1,1,1,2,3,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "eacac72a5da650fd12c8e7a4b54d3ee7f229b9025a4c86a7cd749753364b72b6"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_30
-- END S6_30

-- BEGIN S6_31
namespace S6_31

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,3],[1,1,1,3,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "227c4b03a4c288f4c0152c68bcb6c3544a5f6b4514066249e2275893354bcaeb"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_31
-- END S6_31

-- BEGIN S6_32
namespace S6_32

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,2,2,1,1],[1,1,2,2,1,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "4bf554f55fcb08e4d61d7149191ccb5aeffac1b01655105a0af3293456bf1eb8"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

end S6_32
-- END S6_32

-- BEGIN S6_33
namespace S6_33

/-- Exact one-based order-six catalogue table: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,2,2,1,1],[1,1,2,2,2,1]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9945b50ad276883a8a2309add8c9ba7a79fe18c76c23a316509be6f8c51a8aa9"

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else (4 : Fin 6)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1]

def finiteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩

def finiteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [0]⟩, ⟨0, [1, 2]⟩⟩

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
    BasisFor SemigroupBasis.Generated.Catalogue.S4_2.table.semigroup targetBasis := by
  rw [← SemigroupBasis.Generated.S4_2.table_eq_canonical_catalogue]
  exact SemigroupBasis.Generated.S4_2.representative_basis

theorem representative_basis :
    BasisFor table.semigroup targetBasis :=
  acceptedSourceBasis.inheritAlongEmbedding embedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S6_33
-- END S6_33

end SemigroupBasis.Generated.Order6FinalL5TransferV3

import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S4_69
import SemigroupBasis.Generated.S4_71
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-- The accepted 14-law candidate basis for the `S4_69 x S4_71`
identity-theory intersection. -/
def basis : List (Identity Nat) :=
  [ Identity.mk (w 0 [0])          (w 0 [0, 0]),
    Identity.mk (w 0 [0, 1, 0])    (w 0 [1, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 0, 1]),
    Identity.mk (w 0 [0, 1, 1])    (w 0 [1, 1, 0]),
    Identity.mk (w 0 [0, 1, 1])    (w 1 [0, 0, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]),
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1]),
    Identity.mk (w 0 [1, 0])       (w 0 [1, 0, 0]),
    Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [2, 1, 0, 2]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [2, 1, 2, 0]),
    Identity.mk (w 0 [1, 0, 2, 2]) (w 2 [0, 1, 0, 2]) ]

private def toFinFour : Nat -> Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : List.Mem (identity.map toFinFour) finiteBasis :=
    List.mem_map.mpr (Exists.intro identity (And.intro member rfl))
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinFour).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

set_option maxRecDepth 100000 in
theorem modelsS4_69 :
    Models SemigroupBasis.Generated.S4_69.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S4_69.table (by decide)

set_option maxRecDepth 100000 in
theorem modelsS4_71 :
    Models SemigroupBasis.Generated.S4_71.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S4_71.table (by decide)

/-- Package an unrestricted joint-completeness proof as the shared
intersection basis consumed by every concrete subdirect wrapper. -/
def intersectionBasisOfCompleteness
    (complete :
      forall identity : Identity Nat,
        identity.SatisfiedBy
            SemigroupBasis.Generated.S4_69.table.semigroup ->
          identity.SatisfiedBy
              SemigroupBasis.Generated.S4_71.table.semigroup ->
            Derives basis identity.lhs identity.rhs) :
    IntersectionBasis
      SemigroupBasis.Generated.S4_69.table.semigroup
      SemigroupBasis.Generated.S4_71.table.semigroup basis where
  leftModels := modelsS4_69
  rightModels := modelsS4_71
  complete := complete

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

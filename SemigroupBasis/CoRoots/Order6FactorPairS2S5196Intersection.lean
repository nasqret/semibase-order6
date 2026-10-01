import SemigroupBasis.CoRoots.Order6FactorPairS2S5196
import SemigroupBasis.CoRoots.S5_196Family
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Generated.S2_2
import SemigroupBasis.Subdirect

namespace SemigroupBasis.CoRoots.Order6FactorPairS2S5196Intersection

open SemigroupBasis
open SemigroupBasis.Examples

def basis : List (Identity Nat) :=
  [ Identity.mk (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0, 0]),
    Identity.mk (Word.mk 0 [0, 0, 0, 1]) (Word.mk 0 [0, 1]),
    Identity.mk (Word.mk 0 [0, 0, 1, 0]) (Word.mk 0 [1, 0]),
    Identity.mk (Word.mk 0 [0, 0, 1, 2]) (Word.mk 0 [1, 2]),
    Identity.mk (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 1, 1]),
    Identity.mk (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]),
    Identity.mk (Word.mk 0 [0, 1, 1, 1]) (Word.mk 0 [1, 0]),
    Identity.mk (Word.mk 0 [1, 0]) (Word.mk 0 [1, 1, 1, 0]),
    Identity.mk (Word.mk 0 [1, 0]) (Word.mk 1 [0, 0]),
    Identity.mk (Word.mk 0 [1, 2]) (Word.mk 1 [0, 2]) ]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def finiteBasis : List (Identity (Fin 3)) :=
  basis.map fun identity => identity.map toFinThree

private theorem basisRoundTripChecked :
    basis.all (fun identity =>
      decide ((identity.map toFinThree).map Fin.val = identity)) = true := by
  decide

private theorem modelsOfFiniteChecks
    (table : FiniteTable)
    (checked : finiteBasis.all table.checkIdentity = true) :
    Models table.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinThree ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    table.checkIdentityNat_sound (identity.map toFinThree)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinThree).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp basisRoundTripChecked) identity member
  rw [restored] at finiteValid
  exact finiteValid

theorem modelsS2_2 :
    Models SemigroupBasis.Generated.S2_2.table.semigroup basis :=
  modelsOfFiniteChecks SemigroupBasis.Generated.S2_2.table (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsS5_196 :
    Models SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup basis :=
  modelsOfFiniteChecks
    SemigroupBasis.Generated.Catalogue.S5_196.table (by decide)

/-- The lower `S5_196` factor makes every short valid identity literal; the
long stratum is exactly the Aristotle parity theorem. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy SemigroupBasis.Generated.S2_2.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have exactClass :=
    SemigroupBasis.CoRoots.S5_196Family.S5_196.valid_exactBasisClass
      identity s5Valid
  rcases exactClass with equal | long
  · rw [equal]
    exact Derives.refl _
  · have cyclicValid' :
        identity.SatisfiedBy cyclicTwo.semigroup := by
      rw [← SemigroupBasis.Generated.S2_2.table_eq_catalogue_model]
      exact cyclicValid
    have parity := cyclicValid_parity_eq identity cyclicValid'
    rcases long with ⟨lhsLong, rhsLong, support, simpleFinal⟩
    simpa only [basis] using
      SemigroupBasis.CoRoots.Order6FactorPairS2S5196.derivesLongOfSignatureParity
        identity.lhs identity.rhs lhsLong rhsLong support simpleFinal parity

def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup basis where
  leftModels := modelsS2_2
  rightModels := modelsS5_196
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6FactorPairS2S5196Intersection

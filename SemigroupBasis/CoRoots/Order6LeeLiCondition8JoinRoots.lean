import SemigroupBasis.CoRoots.Order6LeeLiCondition8Join
import SemigroupBasis.FiniteCertificate

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiCondition8JoinRoots

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiCondition8Join

namespace S6_11552

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact `order6-power-i39-opposite-current620-i1` source table for
`S6_11552`, in zero-based form. -/
def packetMul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 4 5 right else
    if left = 1 then row6 0 0 1 1 4 5 right else
      if left = 2 then row6 0 1 2 3 4 5 right else
        if left = 3 then row6 0 1 3 2 4 5 right else
          if left = 4 then row6 0 0 4 4 4 5 right else
            row6 0 4 5 5 4 5 right

def packetTable : FiniteTable where
  order := 6
  mul := packetMul
  assoc := by decide

/-- The canonical Smallsemi representative `S6_11552`. -/
def mul (left right : Fin 6) : Fin 6 :=
  packetMul right left

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 1, 1, 1, 1, 1],
        [1, 1, 2, 2, 1, 5],
        [1, 2, 3, 4, 5, 6],
        [1, 2, 4, 3, 5, 6],
        [5, 5, 5, 5, 5, 5],
        [6, 6, 6, 6, 6, 6]] := by
  decide

def packetTableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (packetTable.semigroup.mul left right).val + 1

theorem packetTableOneBased_certificate :
    packetTableOneBased =
      [[1, 1, 1, 1, 5, 6],
        [1, 1, 2, 2, 5, 6],
        [1, 2, 3, 4, 5, 6],
        [1, 2, 4, 3, 5, 6],
        [1, 1, 5, 5, 5, 6],
        [1, 5, 6, 6, 5, 6]] := by
  decide

/-- The packet source is exactly the opposite of the canonical table. -/
theorem tableOpposite_eq_packet :
    table.semigroup.opposite = packetTable.semigroup := by
  unfold table packetTable mul FiniteTable.semigroup Semigroup.opposite
  rfl

/-- The converse orientation equality used by opposite-basis transport. -/
theorem packetOpposite_eq_table :
    packetTable.semigroup.opposite = table.semigroup := by
  unfold table packetTable mul FiniteTable.semigroup Semigroup.opposite
  rfl

/-! ## Checked join-to-root witnesses -/

/-- The surjective packet coordinate
`[1,1,2,2,5,5,3,4,6,6]`, displayed in one-based form. -/
def primaryValue (value : Fin 5 × Fin 2) : Fin 6 :=
  if value.1 = 0 then 0 else
    if value.1 = 1 then 1 else
      if value.1 = 2 then 4 else
        if value.1 = 3 then
          if value.2 = 0 then 2 else 3
        else 5

def primaryHom :
    Hom joinSemigroup packetTable.semigroup where
  toFun := primaryValue
  map_mul := by
    rintro ⟨leftFirst, leftSecond⟩ ⟨rightFirst, rightSecond⟩
    apply Fin.ext
    exact by decide +revert

private def primaryPreimage (value : Fin 6) : Fin 5 × Fin 2 :=
  if value = 0 then (0, 0) else
    if value = 1 then (1, 0) else
      if value = 2 then (3, 0) else
        if value = 3 then (3, 1) else
          if value = 4 then (2, 0) else (4, 0)

/-- A split quotient proves soundness of the eight laws in the packet table. -/
def packetQuotient :
    SplitSurjection joinSemigroup packetTable.semigroup where
  toFun := primaryValue
  map_mul := primaryHom.map_mul
  preimage := primaryPreimage
  right_inverse := by
    intro value
    apply Fin.ext
    exact by decide +revert

/-- The parity coordinate `[3,4,3,4,3,4,3,4,3,4]`, displayed one-based. -/
def parityValue (value : Fin 5 × Fin 2) : Fin 6 :=
  if value.2 = 0 then 2 else 3

def coordinateHom (coordinate : Fin 2) :
    Hom joinSemigroup packetTable.semigroup where
  toFun := if coordinate = 0 then primaryValue else parityValue
  map_mul := by
    rintro ⟨leftFirst, leftSecond⟩ ⟨rightFirst, rightSecond⟩
    apply Fin.ext
    exact by decide +revert

/-- The two recorded coordinates separate all ten elements of the join. -/
def sourceEmbedding :
    Embedding joinSemigroup (packetTable.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    rintro ⟨leftFirst, leftSecond⟩ ⟨rightFirst, rightSecond⟩
      equalCoordinates
    have coordinateZero := equalCoordinates (0 : Fin 2)
    have coordinateOne := equalCoordinates (1 : Fin 2)
    clear equalCoordinates
    exact by decide +revert)

theorem packetModels : Models packetTable.semigroup basis := by
  intro identity member
  exact packetQuotient.pushforwardIdentity identity
    (leeLiCondition8JoinBasisFor.1 identity member)

/-- Concrete endpoint for the opposite-oriented i39 packet table. -/
theorem packetBasisFor :
    BasisFor packetTable.semigroup basis :=
  leeLiCondition8JoinBasisFor.inheritAlongPowerEmbedding
    sourceEmbedding packetModels

/-- Catalogue-facing endpoint in the orientation recorded by i39. -/
theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite basis := by
  rw [tableOpposite_eq_packet]
  exact packetBasisFor

/-- Catalogue-facing endpoint for the canonical Smallsemi representative. -/
theorem representativeBasisFor :
    BasisFor table.semigroup directBasis := by
  rw [← packetOpposite_eq_table]
  simpa [basis] using packetBasisFor.oppositeReversed

end S6_11552

/-! ## Shared transfer and orientation wrappers -/

universe u v

/-- Transfer the proved packet basis along a point-separating family. -/
theorem packetBasisFor_of_powerEmbedding
    {T : Type u} {I : Type v} {target : Semigroup T}
    (embedding :
      Embedding S6_11552.packetTable.semigroup (target.pi I))
    (targetModels : Models target basis) :
    BasisFor target basis :=
  S6_11552.packetBasisFor.inheritAlongPowerEmbedding
    embedding targetModels

/-- Expose a packet theorem at the campaign's recorded opposite endpoint. -/
theorem oppositeBasisFor_of_packetBasis
    {T : Type u} {packet representative : Semigroup T}
    (representativeOpposite_eq_packet : representative.opposite = packet)
    (packetBasisFor : BasisFor packet basis) :
    BasisFor representative.opposite basis := by
  rw [representativeOpposite_eq_packet]
  exact packetBasisFor

/-- Normalize an opposite-oriented packet theorem to the catalogue table. -/
theorem representativeBasisFor_of_packetBasis
    {T : Type u} {packet representative : Semigroup T}
    (packetOpposite_eq_representative : packet.opposite = representative)
    (packetBasisFor : BasisFor packet basis) :
    BasisFor representative directBasis := by
  rw [← packetOpposite_eq_representative]
  simpa [basis] using packetBasisFor.oppositeReversed

/-- The hand-authored source root for this transfer lane. -/
def joinTransferSourceRootIds : List String :=
  ["S6_11552"]

/-- The exact deterministic WMI discovery population, in Smallsemi order. -/
def joinTransferCandidateRootIds : List String :=
  ["S6_8932", "S6_9073", "S6_11162", "S6_11170", "S6_11550",
    "S6_11554", "S6_11602", "S6_11782"]

/-! ## Independently replayed generated transfers -/

-- BEGIN GENERATED CONDITION8 JOIN TRANSFERS
-- END GENERATED CONDITION8 JOIN TRANSFERS

end SemigroupBasis.CoRoots.Order6LeeLiCondition8JoinRoots

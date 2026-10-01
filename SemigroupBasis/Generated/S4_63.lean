import SemigroupBasis.Generated.S4_72
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_63

open SemigroupBasis
open SemigroupBasis.Examples

/-- The stored Smallsemi representative `S4_63`, with exact table
`[[1,1,1,1],[1,1,1,1],[1,2,3,4],[1,2,3,4]]`. -/
abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_63.table

theorem table_eq_canonical_catalogue :
    table = SemigroupBasis.Generated.Catalogue.S4_63.table := rfl

/-- The diagonal of these two homomorphisms embeds `S4_72ᵒᵖ` into
`S4_63²`. The coordinate maps are `[1,2,1,3]` and `[3,3,4,3]` in
one-based notation. -/
def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_72.table.semigroup.opposite
      (table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then
      if a = 0 then (0 : Fin 4) else
        if a = 1 then (1 : Fin 4) else
          if a = 2 then (0 : Fin 4) else (2 : Fin 4)
    else
      if a = 0 then (2 : Fin 4) else
        if a = 1 then (2 : Fin 4) else
          if a = 2 then (3 : Fin 4) else (2 : Fin 4)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    clear h
    exact by decide +revert

def transferPowerLaw : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLeftDuplicationLaw : Identity Nat :=
  ⟨⟨1, [0]⟩, ⟨1, [1, 0]⟩⟩

def transferRepeatedLastLaw : Identity Nat :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferPrefixCommutationLaw : Identity Nat :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

/-- The word-reversed complete basis inherited from `S4_72ᵒᵖ`. -/
def transferBasis : List (Identity Nat) :=
  [transferPowerLaw, transferLeftDuplicationLaw,
    transferRepeatedLastLaw, transferPrefixCommutationLaw]

theorem transferBasis_eq_source :
    transferBasis = reversedBasis firstRepeatedMarkerFourBasis := rfl

def finiteTransferPowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteTransferLeftDuplicationLaw : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [1, 0]⟩⟩

def finiteTransferRepeatedLastLaw : Identity (Fin 2) :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def finiteTransferPrefixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

theorem finiteTransferPowerLaw_map :
    finiteTransferPowerLaw.map Fin.val = transferPowerLaw := rfl

theorem finiteTransferLeftDuplicationLaw_map :
    finiteTransferLeftDuplicationLaw.map Fin.val =
      transferLeftDuplicationLaw := rfl

theorem finiteTransferRepeatedLastLaw_map :
    finiteTransferRepeatedLastLaw.map Fin.val =
      transferRepeatedLastLaw := rfl

theorem finiteTransferPrefixCommutationLaw_map :
    finiteTransferPrefixCommutationLaw.map Fin.val =
      transferPrefixCommutationLaw := rfl

theorem transferModels :
    Models table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finiteTransferPowerLaw_map]
    exact table.checkIdentityNat_sound finiteTransferPowerLaw (by decide)
  · rw [← finiteTransferLeftDuplicationLaw_map]
    exact table.checkIdentityNat_sound finiteTransferLeftDuplicationLaw
      (by decide)
  · rw [← finiteTransferRepeatedLastLaw_map]
    exact table.checkIdentityNat_sound finiteTransferRepeatedLastLaw
      (by decide)
  · rw [← finiteTransferPrefixCommutationLaw_map]
    exact table.checkIdentityNat_sound finiteTransferPrefixCommutationLaw
      (by decide)

def powerLaw : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def leftDuplicationLaw : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def repeatedLastLaw : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def prefixCommutationLaw : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

/-- The exact displayed basis `xx = xxx`, `xy = xxy`, `xyx = yxx`,
`xyz = yxz`. -/
def basis : List (Identity Nat) :=
  [powerLaw, leftDuplicationLaw, repeatedLastLaw, prefixCommutationLaw]

def finitePowerLaw : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLeftDuplicationLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def finiteRepeatedLastLaw : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def finitePrefixCommutationLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem finitePowerLaw_map :
    finitePowerLaw.map Fin.val = powerLaw := rfl

theorem finiteLeftDuplicationLaw_map :
    finiteLeftDuplicationLaw.map Fin.val = leftDuplicationLaw := rfl

theorem finiteRepeatedLastLaw_map :
    finiteRepeatedLastLaw.map Fin.val = repeatedLastLaw := rfl

theorem finitePrefixCommutationLaw_map :
    finitePrefixCommutationLaw.map Fin.val =
      prefixCommutationLaw := rfl

theorem basis_models :
    Models table.semigroup basis := by
  intro e he
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [← finitePowerLaw_map]
    exact table.checkIdentityNat_sound finitePowerLaw (by decide)
  · rw [← finiteLeftDuplicationLaw_map]
    exact table.checkIdentityNat_sound finiteLeftDuplicationLaw (by decide)
  · rw [← finiteRepeatedLastLaw_map]
    exact table.checkIdentityNat_sound finiteRepeatedLastLaw (by decide)
  · rw [← finitePrefixCommutationLaw_map]
    exact table.checkIdentityNat_sound finitePrefixCommutationLaw (by decide)

private def swapXY : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 0
  | n + 2 => Word.singleton (n + 2)

private def renamePrefix : Nat → Word Nat
  | 0 => Word.singleton 2
  | 1 => Word.singleton 1
  | 2 => Word.singleton 0
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives basis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Derives.fromBasis (e := powerLaw) (by simp [basis])
  · have h : Derives basis leftDuplicationLaw.lhs leftDuplicationLaw.rhs :=
      Derives.fromBasis (e := leftDuplicationLaw) (by simp [basis])
    have renamed := Derives.subst h swapXY
    simpa [transferLeftDuplicationLaw, leftDuplicationLaw, swapXY,
      Word.bind, Word.singleton, Word.append] using renamed
  · exact Derives.symm <|
      Derives.fromBasis (e := repeatedLastLaw) (by simp [basis])
  · have h :
        Derives basis prefixCommutationLaw.lhs prefixCommutationLaw.rhs :=
      Derives.fromBasis (e := prefixCommutationLaw) (by simp [basis])
    have renamed := Derives.subst h renamePrefix
    simpa [transferPrefixCommutationLaw, prefixCommutationLaw, renamePrefix,
      Word.bind, Word.singleton, Word.append] using renamed

theorem transferred_basis :
    BasisFor table.semigroup transferBasis := by
  have inherited :
      BasisFor table.semigroup
        (reversedBasis firstRepeatedMarkerFourBasis) :=
    SemigroupBasis.Generated.S4_72.opposite_basis.inheritAlongPowerEmbedding
      powerEmbedding
      (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor table.semigroup basis :=
  transferred_basis.replace basis_models transferAxiomsDerive

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.S4_63

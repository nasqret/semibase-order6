import SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_10406

open SemigroupBasis

def routeManifestRowSHA256 : String := "6ab51bebd5dbdfa6047fa14ce074208bdacd80d1dbde5ed660a7c72a862bcb2b"
def witnessRecordSHA256 : String := "6f4cb21127053f796a7338a654389249d8d72ecd13c1b83c474b8c0284986ad0"
def sourceTableSHA256 : String := "4bef1b26dba5071058832088214d7814fd3d200be6fdb81b146872bc71835c66"
def targetTableSHA256 : String := "85ab3f38601e809e172b7a8921a069ecd3f3287b846468c8d491f022fe1b8a62"

/-- Exact selected target table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,2,3,4,5,6],[1,2,4,3,5,6],[1,2,5,6,5,6],[1,2,6,5,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based separating maps: `[[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,3,4,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,3,1],[1,1,2,3,3,1],[1,1,1,3,4,1],[6,6,6,3,4,5]]

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (3 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceSemigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceSemigroup
      (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0]⟩, ⟨1, [1, 1, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [0, 1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0, 0]⟩⟩

def finiteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 1, 0]⟩⟩

def finiteLaw5 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1, 1, 0]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [1, 2, 1, 0]⟩⟩

def finiteLaw7 : Identity (Fin 2) :=
  ⟨⟨1, [0, 0, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw8 : Identity (Fin 2) :=
  ⟨⟨1, [0, 1, 0]⟩, ⟨0, [1, 1, 0]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨1, [0, 2, 1, 0]⟩, ⟨0, [1, 2, 1, 0]⟩⟩

def finiteLaw10 : Identity (Fin 3) :=
  ⟨⟨2, [0, 2, 1, 0]⟩, ⟨0, [2, 2, 1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw5 := rfl

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw6 := rfl

theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw7 := rfl

theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw8 := rfl

theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw9 := rfl

theorem finiteLaw10_map :
    finiteLaw10.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceLaw10 := rfl

theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)
  · subst e
    rw [← finiteLaw3_map]
    exact table.checkIdentityNat_sound finiteLaw3 (by decide)
  · subst e
    rw [← finiteLaw4_map]
    exact table.checkIdentityNat_sound finiteLaw4 (by decide)
  · subst e
    rw [← finiteLaw5_map]
    exact table.checkIdentityNat_sound finiteLaw5 (by decide)
  · subst e
    rw [← finiteLaw6_map]
    exact table.checkIdentityNat_sound finiteLaw6 (by decide)
  · subst e
    rw [← finiteLaw7_map]
    exact table.checkIdentityNat_sound finiteLaw7 (by decide)
  · subst e
    rw [← finiteLaw8_map]
    exact table.checkIdentityNat_sound finiteLaw8 (by decide)
  · subst e
    rw [← finiteLaw9_map]
    exact table.checkIdentityNat_sound finiteLaw9 (by decide)
  · subst e
    rw [← finiteLaw10_map]
    exact table.checkIdentityNat_sound finiteLaw10 (by decide)

theorem selected_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.basis_complete sourceEmbedding targetModels

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceBasis) :=
  selected_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_6198Opposite.sourceBasis)) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_10406

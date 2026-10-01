import SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_14258

open SemigroupBasis

def routeManifestRowSHA256 : String := "a1265b51edcd3b6a77baba7bfeb68cb9af2d42652bb3294694658d6caa1c4ed0"
def witnessRecordSHA256 : String := "9beb5a9af032d97c35896e1cc4ad43e103751fa8a19253d22022601926dada72"
def sourceTableSHA256 : String := "dbe2a11fc315d8f688cb623874e23956071d1f6636c932733b05f5c231e5c61c"
def targetTableSHA256 : String := "181ed41f80ad3d5c41e081831eceb9c42c494a5d34e525847f64fbec900ac697"

/-- Exact selected target table, one-based: `[[1,1,1,1,5,6],[1,1,1,2,5,6],[3,3,3,3,5,6],[1,2,1,4,5,6],[5,5,5,5,5,6],[6,6,6,6,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based separating maps: `[[1,2,1,1,1,1],[5,5,5,5,1,1],[6,6,6,5,1,1],[5,5,5,5,3,1],[1,1,2,1,4,4]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[5,5,5,5,1,1],[6,6,6,5,1,1],[5,5,5,5,3,1],[1,1,2,1,4,4]]

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (3 : Fin 6) else (3 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceSemigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceSemigroup
      (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [1, 0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨0, [0, 1, 0]⟩⟩

def finiteLaw3 : Identity (Fin 2) :=
  ⟨⟨1, [1, 0, 0]⟩, ⟨1, [0, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨2, [1, 0, 0]⟩, ⟨2, [0, 1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceLaw4 := rfl

theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
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

theorem selected_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.basis_complete sourceEmbedding targetModels

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceBasis) :=
  selected_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7648Opposite.sourceBasis)) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_14258

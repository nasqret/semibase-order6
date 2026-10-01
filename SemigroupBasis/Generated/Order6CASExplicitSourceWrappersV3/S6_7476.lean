import SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_7476

open SemigroupBasis

def routeManifestRowSHA256 : String := "6ebf80c286ba892e9818c28533a70047dcac66167d43de65784ea16b20c2ba31"
def witnessRecordSHA256 : String := "8af51b38d321fbedb734cbaf84ed49e216ecf8524788d6739fe939c321599073"
def sourceTableSHA256 : String := "d2edf23280eb6cfbeb1dedfdcd5110808b16aa702f9653706608c5a1e074db3b"
def targetTableSHA256 : String := "1ac36c908b147b1fd34f9805ddf3d612e7c140370849327bee05a854875fcf93"

/-- Exact selected target table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,3],[1,2,1,4,5,4],[1,2,1,4,5,5],[1,2,1,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based separating maps: `[[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,1,2,1,4],[1,1,3,1,1,6],[5,5,5,5,4,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,1,1,4],[1,1,1,2,1,4],[1,1,3,1,1,6],[5,5,5,5,4,6]]

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (0 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (3 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceSemigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceSemigroup
      (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

def finiteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def finiteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def finiteLaw2 : Identity (Fin 3) :=
  ⟨⟨2, [1, 0]⟩, ⟨2, [1, 1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceLaw2 := rfl

theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← finiteLaw0_map]
    exact table.checkIdentityNat_sound finiteLaw0 (by decide)
  · subst e
    rw [← finiteLaw1_map]
    exact table.checkIdentityNat_sound finiteLaw1 (by decide)
  · subst e
    rw [← finiteLaw2_map]
    exact table.checkIdentityNat_sound finiteLaw2 (by decide)

theorem selected_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.basis_complete sourceEmbedding targetModels

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceBasis) :=
  selected_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_3306Opposite.sourceBasis)) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_7476

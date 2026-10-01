import SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_13009

open SemigroupBasis

def routeManifestRowSHA256 : String := "c609bdea292cf36a81e0ca2239ba0e14e252067d6596c0b068d2747de919f31c"
def witnessRecordSHA256 : String := "86d0dde980b39068f38f553e9d123be97f15da7dd17b1b139ac5ca52894afd4d"
def sourceTableSHA256 : String := "7828996f1719c5f463211554aa0b8e9f2f25d5c72fa04e93755b78cb7bc03f0c"
def targetTableSHA256 : String := "ae29b2fa5529e872b43f887c7b111139e23e048a3c5b3f680e46febc30645040"

/-- Exact selected target table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,2],[1,2,3,3,5,1],[1,2,3,4,5,1],[1,2,3,5,5,1],[1,1,1,1,1,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based separating maps: `[[1,2,1,1,1,1],[1,1,1,3,1,1],[1,1,1,1,1,3],[1,1,2,6,1,3],[5,5,5,5,3,4]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,1,3,1,1],[1,1,1,1,1,3],[1,1,2,6,1,3],[5,5,5,5,3,4]]

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (2 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (2 : Fin 6) else (3 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceSemigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceSemigroup
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
  ⟨⟨0, [1, 0]⟩, ⟨1, [1, 0, 0]⟩⟩

def finiteLaw3 : Identity (Fin 3) :=
  ⟨⟨2, [0, 1, 0]⟩, ⟨2, [0, 1, 1, 0, 1, 0]⟩⟩

def finiteLaw4 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [0, 2, 1, 0]⟩⟩

def finiteLaw5 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨2, [0, 2, 1, 0]⟩⟩

def finiteLaw6 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨2, [1, 1, 2, 1, 0, 0]⟩⟩

def finiteLaw7 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨1, [2, 1, 0, 0, 1, 0]⟩⟩

def finiteLaw8 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨2, [2, 1, 0, 0, 1, 0]⟩⟩

def finiteLaw9 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 0, 1, 0, 1, 0]⟩⟩

def finiteLaw10 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨1, [2, 0, 1, 0, 1, 0]⟩⟩

def finiteLaw11 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 1, 0, 1, 0]⟩⟩

def finiteLaw12 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 1, 0, 1, 0]⟩⟩

def finiteLaw13 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨2, [0, 1, 2, 0, 1, 0]⟩⟩

def finiteLaw14 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨1, [0, 2, 2, 0, 1, 0]⟩⟩

def finiteLaw15 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 2, 0, 1, 0]⟩⟩

def finiteLaw16 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 2, 0, 1, 1, 0]⟩⟩

def finiteLaw17 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 0, 2, 1, 0]⟩⟩

def finiteLaw18 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨2, [0, 1, 1, 2, 1, 0]⟩⟩

def finiteLaw19 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 1, 1, 2, 1, 0]⟩⟩

def finiteLaw20 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨1, [0, 2, 1, 2, 1, 0]⟩⟩

def finiteLaw21 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [1, 2, 1, 2, 1, 0]⟩⟩

def finiteLaw22 : Identity (Fin 3) :=
  ⟨⟨0, [2, 1, 0]⟩, ⟨0, [2, 2, 1, 2, 1, 0]⟩⟩

def finiteLaw23 : Identity (Fin 3) :=
  ⟨⟨1, [2, 1, 0]⟩, ⟨1, [2, 2, 1, 2, 1, 0]⟩⟩

theorem finiteLaw0_map :
    finiteLaw0.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw0 := rfl

theorem finiteLaw1_map :
    finiteLaw1.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw1 := rfl

theorem finiteLaw2_map :
    finiteLaw2.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw2 := rfl

theorem finiteLaw3_map :
    finiteLaw3.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw3 := rfl

theorem finiteLaw4_map :
    finiteLaw4.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw4 := rfl

theorem finiteLaw5_map :
    finiteLaw5.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw5 := rfl

theorem finiteLaw6_map :
    finiteLaw6.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw6 := rfl

theorem finiteLaw7_map :
    finiteLaw7.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw7 := rfl

theorem finiteLaw8_map :
    finiteLaw8.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw8 := rfl

theorem finiteLaw9_map :
    finiteLaw9.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw9 := rfl

theorem finiteLaw10_map :
    finiteLaw10.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw10 := rfl

theorem finiteLaw11_map :
    finiteLaw11.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw11 := rfl

theorem finiteLaw12_map :
    finiteLaw12.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw12 := rfl

theorem finiteLaw13_map :
    finiteLaw13.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw13 := rfl

theorem finiteLaw14_map :
    finiteLaw14.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw14 := rfl

theorem finiteLaw15_map :
    finiteLaw15.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw15 := rfl

theorem finiteLaw16_map :
    finiteLaw16.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw16 := rfl

theorem finiteLaw17_map :
    finiteLaw17.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw17 := rfl

theorem finiteLaw18_map :
    finiteLaw18.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw18 := rfl

theorem finiteLaw19_map :
    finiteLaw19.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw19 := rfl

theorem finiteLaw20_map :
    finiteLaw20.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw20 := rfl

theorem finiteLaw21_map :
    finiteLaw21.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw21 := rfl

theorem finiteLaw22_map :
    finiteLaw22.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw22 := rfl

theorem finiteLaw23_map :
    finiteLaw23.map Fin.val = SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceLaw23 := rfl

set_option maxHeartbeats 1000000 in
theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceBasis) := by
  intro e he
  simp only [SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
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
  · subst e
    rw [← finiteLaw11_map]
    exact table.checkIdentityNat_sound finiteLaw11 (by decide)
  · subst e
    rw [← finiteLaw12_map]
    exact table.checkIdentityNat_sound finiteLaw12 (by decide)
  · subst e
    rw [← finiteLaw13_map]
    exact table.checkIdentityNat_sound finiteLaw13 (by decide)
  · subst e
    rw [← finiteLaw14_map]
    exact table.checkIdentityNat_sound finiteLaw14 (by decide)
  · subst e
    rw [← finiteLaw15_map]
    exact table.checkIdentityNat_sound finiteLaw15 (by decide)
  · subst e
    rw [← finiteLaw16_map]
    exact table.checkIdentityNat_sound finiteLaw16 (by decide)
  · subst e
    rw [← finiteLaw17_map]
    exact table.checkIdentityNat_sound finiteLaw17 (by decide)
  · subst e
    rw [← finiteLaw18_map]
    exact table.checkIdentityNat_sound finiteLaw18 (by decide)
  · subst e
    rw [← finiteLaw19_map]
    exact table.checkIdentityNat_sound finiteLaw19 (by decide)
  · subst e
    rw [← finiteLaw20_map]
    exact table.checkIdentityNat_sound finiteLaw20 (by decide)
  · subst e
    rw [← finiteLaw21_map]
    exact table.checkIdentityNat_sound finiteLaw21 (by decide)
  · subst e
    rw [← finiteLaw22_map]
    exact table.checkIdentityNat_sound finiteLaw22 (by decide)
  · subst e
    rw [← finiteLaw23_map]
    exact table.checkIdentityNat_sound finiteLaw23 (by decide)

theorem selected_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceBasis) :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.basis_complete sourceEmbedding targetModels

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceBasis) :=
  selected_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6CASExplicitSourceAdapters.S6_7391Opposite.sourceBasis)) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6CASExplicitSourceWrappersV3.S6_13009

import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_20
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_20Transfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_76
namespace S5_76

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_76.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_76.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_76.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_76.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_76.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_76.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_76.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_76.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_76.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_76.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_76.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_76.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_76
-- END S5_76

-- BEGIN S5_78
namespace S5_78

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_78.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_78.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_78.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_78.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_78.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_78.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_78.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_78.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_78.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_78.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_78.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_78.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_78.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_78
-- END S5_78

-- BEGIN S5_80
namespace S5_80

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_80.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_80.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_80.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_80.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_80.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_80.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_80.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_80.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_80.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_80.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_80.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_80.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_80.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_80
-- END S5_80

-- BEGIN S5_86
namespace S5_86

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (1 : Fin 5) else if b = 3 then (0 : Fin 5) else (3 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (0 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_86.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.S4_20.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_86.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_86.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_86.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_86.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_86.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_86.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_86.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_86.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_86.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_86.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_86.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_86
-- END S5_86

-- BEGIN S5_90
namespace S5_90

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_90.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_90.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_90.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_90.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_90.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_90.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_90.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_90.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_90.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_90.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_90.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_90.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_90
-- END S5_90

-- BEGIN S5_244
namespace S5_244

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_244.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_244.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_244.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_244.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_244.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_244.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_244.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_244.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_244.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_244.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_244.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_244.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_244
-- END S5_244

-- BEGIN S5_320
namespace S5_320

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_320.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_320.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_320.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_320.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_320.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_320.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_320.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_320.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_320.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_320.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_320.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_320.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_320
-- END S5_320

-- BEGIN S5_323
namespace S5_323

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_323.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_323.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_323.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_323.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_323.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_323.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_323.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_323.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_323.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_323.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_323.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_323.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_323
-- END S5_323

-- BEGIN S5_331
namespace S5_331

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_331.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else (3 : Fin 5)
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

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_331.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_331.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_331.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_331.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_331.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_331.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_331.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_331.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_331.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_331.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_331.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_331
-- END S5_331

-- BEGIN S5_333
namespace S5_333

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_333.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_333.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_333.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_333.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_333.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_333.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_333.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_333.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_333.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_333.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_333.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_333.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_333.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_333
-- END S5_333

-- BEGIN S5_352
namespace S5_352

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_352.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_352.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_352.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_352.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_352.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_352.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_352.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_352.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_352.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_352.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_352.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_352.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_352
-- END S5_352

-- BEGIN S5_422
namespace S5_422

def embedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_422.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_422.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_422.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_422.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_422.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_422.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_422.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_422.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_422.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_422.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_422.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_422.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_422
-- END S5_422

-- BEGIN S5_551
namespace S5_551

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (3 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_551.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.S4_20.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_551.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_551.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_551.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_551.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_551.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_551.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_551.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_551.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_551.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_551.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_551.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_551.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_551
-- END S5_551

-- BEGIN S5_568
namespace S5_568

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_20.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_568.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else (2 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
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

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_568.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_568.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_568.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_568.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 1, 2]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_568.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_568.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_568.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_568.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    have h : Derives targetBasis targetLaw0.lhs targetLaw0.rhs :=
      Derives.fromBasis (e := targetLaw0) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst0
    simpa [transferLaw0, targetLaw0, bridgeSubst0, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw1.lhs targetLaw1.rhs :=
      Derives.fromBasis (e := targetLaw1) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst1
    simpa [transferLaw1, targetLaw1, bridgeSubst1, Word.bind, Word.singleton, Word.append] using renamed
  · subst e
    have h : Derives targetBasis targetLaw2.lhs targetLaw2.rhs :=
      Derives.fromBasis (e := targetLaw2) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (simpleEndpointsBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_568.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_568.table.semigroup
        (simpleEndpointsBasis) :=
    SemigroupBasis.Generated.S4_20.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_568.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_568.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_568
-- END S5_568

end SemigroupBasis.Generated.S4_20Transfers

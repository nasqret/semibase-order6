import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_71
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_71Transfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_329
namespace S5_329

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_329.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_329.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_329.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_329.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_329.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_329.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_329.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_329.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_329.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_329.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_329.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_329.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_329.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_329
-- END S5_329

-- BEGIN S5_330
namespace S5_330

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_330.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_330.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_330.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_330.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_330.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_330.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_330.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_330.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_330.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_330.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_330.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_330.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_330.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_330
-- END S5_330

-- BEGIN S5_337
namespace S5_337

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_337.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_337.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_337.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_337.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_337.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_337.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_337.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_337.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_337.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_337.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_337.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_337.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_337.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_337
-- END S5_337

-- BEGIN S5_364
namespace S5_364

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_364.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_364.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_364.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_364.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_364.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_364.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_364.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_364.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_364.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_364.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_364.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_364.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_364.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_364
-- END S5_364

-- BEGIN S5_365
namespace S5_365

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_365.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_365.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_365.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_365.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_365.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_365.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_365.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_365.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_365.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_365.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_365.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_365.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_365.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_365
-- END S5_365

-- BEGIN S5_368
namespace S5_368

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_368.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_368.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_368.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_368.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_368.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_368.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_368.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_368.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_368.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_368.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_368.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_368.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_368.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_368
-- END S5_368

-- BEGIN S5_380
namespace S5_380

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_380.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_380.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_380.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_380.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_380.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_380.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_380.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_380.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_380.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_380.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_380.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_380.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_380.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_380
-- END S5_380

-- BEGIN S5_382
namespace S5_382

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_382.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_382.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_382.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_382.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_382.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_382.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_382.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_382.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_382.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_382.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_382.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_382.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_382.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_382
-- END S5_382

-- BEGIN S5_385
namespace S5_385

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_385.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_385.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_385.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_385.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_385.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_385.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_385.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_385.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_385.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_385.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_385.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_385.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_385.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_385
-- END S5_385

-- BEGIN S5_401
namespace S5_401

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_401.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_401.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_401.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_401.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_401.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_401.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_401.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_401.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_401.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_401.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_401.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_401.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_401.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_401
-- END S5_401

-- BEGIN S5_411
namespace S5_411

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (2 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_411.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.S4_71.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (0 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_411.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_411.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_411.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_411.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_411.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_411.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_411.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_411.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_411.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_411.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_411.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_411.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_411
-- END S5_411

-- BEGIN S5_608
namespace S5_608

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_608.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_608.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_608.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_608.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_608.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_608.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_608.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_608.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_608.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_608.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_608.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_608.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_608.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_608
-- END S5_608

-- BEGIN S5_609
namespace S5_609

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_609.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_609.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_609.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_609.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_609.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_609.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_609.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_609.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_609.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_609.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_609.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_609.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_609.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_609
-- END S5_609

-- BEGIN S5_611
namespace S5_611

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_611.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_611.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_611.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_611.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_611.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_611.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_611.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_611.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_611.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_611.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_611.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_611.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_611.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_611
-- END S5_611

-- BEGIN S5_630
namespace S5_630

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_630.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_630.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_630.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_630.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_630.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_630.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_630.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_630.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_630.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_630.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_630.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_630.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_630.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_630
-- END S5_630

-- BEGIN S5_760
namespace S5_760

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_760.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_760.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_760.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_760.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_760.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_760.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_760.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_760.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_760.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_760.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_760.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_760.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_760.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_760
-- END S5_760

-- BEGIN S5_769
namespace S5_769

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_769.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_769.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_769.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_769.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_769.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_769.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_769.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_769.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_769.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_769.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_769.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_769.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_769.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_769
-- END S5_769

-- BEGIN S5_781
namespace S5_781

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_781.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_781.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_781.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_781.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_781.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_781.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_781.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_781.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_781.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_781.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_781.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_781.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_781.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_781
-- END S5_781

-- BEGIN S5_799
namespace S5_799

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_799.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_799.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_799.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_799.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_799.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_799.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_799.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_799.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_799.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_799.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_799.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_799.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_799.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_799
-- END S5_799

-- BEGIN S5_800
namespace S5_800

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_800.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_800.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_800.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_800.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_800.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_800.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_800.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_800.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_800.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_800.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_800.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_800.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_800.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_800
-- END S5_800

-- BEGIN S5_842
namespace S5_842

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_842.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_842.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_842.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_842.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_842.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_842.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_842.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_842.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_842.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_842.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_842.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_842.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_842.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_842
-- END S5_842

-- BEGIN S5_898
namespace S5_898

def embedding :
    Embedding SemigroupBasis.Generated.S4_71.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_898.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_898.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_898.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_898.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_898.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_898.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_898.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_898.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_898.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourSeventyOneBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_898.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_898.table.semigroup
        (edmundsFourSeventyOneBasis) :=
    SemigroupBasis.Generated.S4_71.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_898.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_898.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_898
-- END S5_898

end SemigroupBasis.Generated.S4_71Transfers

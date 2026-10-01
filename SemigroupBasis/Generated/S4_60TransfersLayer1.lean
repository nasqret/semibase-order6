import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_60
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_60Transfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_298
namespace S5_298

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_298.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_298.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_298.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_298.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_298.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_298.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_298.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_298.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_298.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_298.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_298.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_298.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_298.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_298.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_298.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_298
-- END S5_298

-- BEGIN S5_305
namespace S5_305

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_305.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_305.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_305.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_305.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_305.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_305.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_305.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_305.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_305.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_305.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_305.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_305.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_305.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_305.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_305.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_305
-- END S5_305

-- BEGIN S5_312
namespace S5_312

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_312.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_312.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_312.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_312.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_312.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_312.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_312.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_312.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_312.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_312.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_312.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_312.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_312.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_312.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_312.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_312
-- END S5_312

-- BEGIN S5_564
namespace S5_564

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_564.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_564.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_564.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_564.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_564.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_564.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_564.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_564.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_564.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_564.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_564.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_564.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_564.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_564.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_564.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_564
-- END S5_564

-- BEGIN S5_584
namespace S5_584

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_584.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_584.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_584.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_584.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_584.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_584.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_584.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_584.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_584.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_584.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_584.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_584.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_584.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_584.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_584.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_584
-- END S5_584

-- BEGIN S5_585
namespace S5_585

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_585.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_585.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_585.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_585.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_585.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_585.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_585.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_585.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_585.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_585
-- END S5_585

-- BEGIN S5_680
namespace S5_680

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_680.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_680.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_680.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_680.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_680.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_680.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_680.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_680.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_680.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_680.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_680.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_680.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_680.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_680.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_680.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_680
-- END S5_680

-- BEGIN S5_690
namespace S5_690

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_690.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (0 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
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
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_690.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_690.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_690.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_690.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_690.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_690.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_690.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_690.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_690.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_690.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_690.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_690.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_690.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_690.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_690
-- END S5_690

-- BEGIN S5_695
namespace S5_695

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_695.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_695.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_695.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_695.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_695.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_695.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_695.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_695.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_695.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_695.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_695.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_695.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_695.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_695.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_695.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_695
-- END S5_695

-- BEGIN S5_710
namespace S5_710

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_710.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (0 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
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
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_710.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_710.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_710.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_710.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_710.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_710.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_710.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_710.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_710.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_710.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_710.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_710.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_710.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_710.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_710
-- END S5_710

-- BEGIN S5_725
namespace S5_725

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_725.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_725.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_725.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_725.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_725.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_725.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_725.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_725.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_725.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_725.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_725.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_725.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_725.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_725.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_725.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_725
-- END S5_725

-- BEGIN S5_726
namespace S5_726

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_726.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_726.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_726.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_726.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_726.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_726.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_726.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_726.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_726.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_726.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_726.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_726.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_726.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_726.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_726.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_726
-- END S5_726

-- BEGIN S5_727
namespace S5_727

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_727.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_727.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_727.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_727.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_727.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_727.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_727.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_727.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_727.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_727.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_727.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_727.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_727.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_727.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_727.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_727
-- END S5_727

-- BEGIN S5_729
namespace S5_729

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_729.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_729.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_729.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_729.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_729.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_729.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_729.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_729.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_729.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_729.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_729.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_729.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_729.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_729.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_729.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_729
-- END S5_729

-- BEGIN S5_887
namespace S5_887

def embedding :
    Embedding SemigroupBasis.Generated.S4_60.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_887.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_887.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_887.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_887.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_887.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_887.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_887.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_887.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_887.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_887.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_887.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_887.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_887.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_887.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_887.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_887
-- END S5_887

-- BEGIN S5_912
namespace S5_912

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if a = 3 then if b = 0 then (3 : Fin 5) else if b = 1 then (3 : Fin 5) else if b = 2 then (3 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if b = 0 then (4 : Fin 5) else if b = 1 then (4 : Fin 5) else if b = 2 then (4 : Fin 5) else if b = 3 then (4 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_912.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.S4_60.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (0 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_912.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_912.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_912.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_912.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_912.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 0, 2]⟩, ⟨0, [0, 1, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 1]⟩, ⟨0, [2, 1, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2, 2]⟩, ⟨0, [2, 1, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_912.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_912.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_912.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_912.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_912.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw3.lhs targetLaw3.rhs :=
      Derives.fromBasis (e := targetLaw3) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst3
    simpa [transferLaw3, targetLaw3, bridgeSubst3, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (edmundsFourSixtyBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_912.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_912.table.semigroup
        (edmundsFourSixtyBasis) :=
    SemigroupBasis.Generated.S4_60.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_912.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_912.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_912
-- END S5_912

end SemigroupBasis.Generated.S4_60Transfers

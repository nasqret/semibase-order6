import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_27
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.S4_27Transfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_116
namespace S5_116

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_116.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_116.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_116.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_116.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_116.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_116.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_116.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_116.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_116.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_116.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_116.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_116.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_116.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_116.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_116.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_116
-- END S5_116

-- BEGIN S5_117
namespace S5_117

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_117.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_117.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_117.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_117.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_117.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_117.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_117.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_117.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_117.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_117.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_117.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_117.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_117.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_117.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_117.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_117
-- END S5_117

-- BEGIN S5_118
namespace S5_118

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_118.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_118.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_118.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_118.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_118.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_118.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_118.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_118.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_118.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_118.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_118.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_118.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_118.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_118.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_118.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_118
-- END S5_118

-- BEGIN S5_128
namespace S5_128

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_128.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_128.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_128.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_128.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_128.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_128.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_128.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_128.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_128.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_128.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_128.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_128.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_128.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_128.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_128.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_128
-- END S5_128

-- BEGIN S5_129
namespace S5_129

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_129.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_129.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_129.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_129.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_129.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_129.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_129.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_129.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_129.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_129.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_129.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_129.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_129.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_129.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_129.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_129
-- END S5_129

-- BEGIN S5_262
namespace S5_262

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_262.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_262.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_262.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_262.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_262.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_262.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_262.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_262.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_262.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_262.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_262.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_262.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_262.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_262.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_262.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_262
-- END S5_262

-- BEGIN S5_263
namespace S5_263

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_263.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_263.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_263.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_263.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_263.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_263.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_263.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_263.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_263.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_263.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_263.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_263.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_263.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_263.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_263.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_263
-- END S5_263

-- BEGIN S5_432
namespace S5_432

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_432.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_432.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_432.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_432.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_432.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_432.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_432.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_432.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_432.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_432.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_432.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_432.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_432.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_432.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_432.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_432
-- END S5_432

-- BEGIN S5_435
namespace S5_435

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_435.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_435.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_435.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_435.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_435.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_435.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_435.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_435.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_435.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_435.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_435.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_435.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_435.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_435.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_435.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_435
-- END S5_435

-- BEGIN S5_436
namespace S5_436

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_436.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_436.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_436.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_436.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_436.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_436.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_436.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_436.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_436.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_436.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_436.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_436.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_436.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_436.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_436.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_436
-- END S5_436

-- BEGIN S5_447
namespace S5_447

def embedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_447.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_447.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_447.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_447.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_447.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_447.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_447.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_447.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_447.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_447.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_447.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_447.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_447.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_447.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_447.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_447
-- END S5_447

-- BEGIN S5_556
namespace S5_556

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_556.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else (4 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (2 : Fin 5)
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
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_556.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_556.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_556.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_556.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_556.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_556.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_556.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_556.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_556.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_556.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_556.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_556.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_556.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_556.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_556
-- END S5_556

-- BEGIN S5_559
namespace S5_559

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_27.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_559.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else (4 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (2 : Fin 5)
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
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_559.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_559.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_559.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_559.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_559.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_559.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_559.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_559.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_559.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_559.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_559.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_559.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_559.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_559.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_559
-- END S5_559

-- BEGIN S5_654
namespace S5_654

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (2 : Fin 5) else if a = 3 then if b = 0 then (3 : Fin 5) else if b = 1 then (3 : Fin 5) else if b = 2 then (3 : Fin 5) else if b = 3 then (2 : Fin 5) else (3 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_654.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.S4_27.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_654.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_654.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_654.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_654.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_654.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1, 1]⟩, ⟨1, [1, 0, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0, 1]⟩, ⟨0, [1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1, 1]⟩, ⟨1, [0, 0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_654.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_654.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_654.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_654.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_654.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst3 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
    transferBasis = (edmundsFourTwentySevenBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_654.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_654.table.semigroup
        (edmundsFourTwentySevenBasis) :=
    SemigroupBasis.Generated.S4_27.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_654.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_654.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_654
-- END S5_654

end SemigroupBasis.Generated.S4_27Transfers

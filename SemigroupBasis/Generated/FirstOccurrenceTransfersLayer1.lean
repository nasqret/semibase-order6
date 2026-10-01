import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_59
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

namespace SemigroupBasis.Generated.FirstOccurrenceTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S4_87
namespace S4_87

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S4_87.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (2 : Fin 4) else if a = 1 then (2 : Fin 4) else if a = 2 then (0 : Fin 4) else (3 : Fin 4) else if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else (0 : Fin 4)
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
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S4_87.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_87.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_87.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_87.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S4_87.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S4_87.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S4_87.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S4_87.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_87.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S4_87.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_87.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_87.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S4_87
-- END S4_87

-- BEGIN S5_296
namespace S5_296

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_296.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_296.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_296.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_296.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_296.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_296.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_296.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_296.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_296.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_296.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_296.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_296.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_296.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_296
-- END S5_296

-- BEGIN S5_554
namespace S5_554

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_554.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_554.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_554.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_554.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_554.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_554.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_554.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_554.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_554.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_554.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_554.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_554.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_554.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_554
-- END S5_554

-- BEGIN S5_582
namespace S5_582

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_582.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_582.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_582.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_582.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_582.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_582.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_582.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_582.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_582.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_582.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_582.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_582.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_582.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_582
-- END S5_582

-- BEGIN S5_679
namespace S5_679

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_679.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_679.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_679.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_679.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_679.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_679.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_679.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_679.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_679.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_679.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_679.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_679.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_679.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_679
-- END S5_679

-- BEGIN S5_693
namespace S5_693

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_693.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_693.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_693.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_693.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_693.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_693.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_693.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_693.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_693.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_693.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_693.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_693.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_693.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_693
-- END S5_693

-- BEGIN S5_701
namespace S5_701

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_701.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_701.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_701.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_701.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_701.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_701.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_701.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_701.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_701.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_701.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_701.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_701.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_701.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_701
-- END S5_701

-- BEGIN S5_708
namespace S5_708

def powerEmbedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_708.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 4) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (0 : Fin 5) else if a = 0 then (2 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
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
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_708.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_708.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_708.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_708.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_708.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_708.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_708.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_708.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_708.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_708.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_708.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_708.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_708
-- END S5_708

-- BEGIN S5_715
namespace S5_715

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_715.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_715.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_715.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_715.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_715.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_715.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_715.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_715.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_715.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_715.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_715.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_715.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_715.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_715
-- END S5_715

-- BEGIN S5_716
namespace S5_716

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_716.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_716.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_716.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_716.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_716.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_716.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_716.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_716.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_716.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_716.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_716.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_716.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_716.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_716
-- END S5_716

-- BEGIN S5_720
namespace S5_720

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_720.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_720.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_720.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_720.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_720.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_720.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_720.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_720.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_720.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_720.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_720.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_720.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_720.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_720
-- END S5_720

-- BEGIN S5_721
namespace S5_721

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_721.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_721.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_721.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_721.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_721.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_721.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_721.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_721.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_721.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_721.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_721.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_721.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_721.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_721
-- END S5_721

-- BEGIN S5_723
namespace S5_723

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_723.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_723.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_723.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_723.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_723.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_723.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_723.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_723.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_723.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_723.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_723.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_723.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_723.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_723
-- END S5_723

-- BEGIN S5_724
namespace S5_724

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_724.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_724.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_724.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_724.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_724.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_724.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_724.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_724.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_724.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_724.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_724.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_724.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_724.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_724
-- END S5_724

-- BEGIN S5_754
namespace S5_754

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 2 then if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 3 then if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5) else if b = 0 then (4 : Fin 5) else if b = 1 then (4 : Fin 5) else if b = 2 then (4 : Fin 5) else if b = 3 then (4 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_754.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.S4_59.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_754.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_754.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_754.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_754.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_754.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_754.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_754.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_754.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_754.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_754.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_754.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_754.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_754
-- END S5_754

-- BEGIN S5_886
namespace S5_886

def embedding :
    Embedding SemigroupBasis.Generated.S4_59.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_886.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_886.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_886.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_886.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_886.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_886.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_886.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_886.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_886.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_886.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_886.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_886.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_886.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_886
-- END S5_886

-- BEGIN S5_910
namespace S5_910

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5) else if a = 3 then if b = 0 then (3 : Fin 5) else if b = 1 then (3 : Fin 5) else if b = 2 then (3 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if b = 0 then (4 : Fin 5) else if b = 1 then (4 : Fin 5) else if b = 2 then (4 : Fin 5) else if b = 3 then (4 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_910.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.S4_59.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (2 : Fin 4) else if a = 3 then (0 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (2 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_910.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_910.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_910.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_910.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_910.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_910.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_910.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_910.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_910.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_910.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_910.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_910.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_910
-- END S5_910

-- BEGIN S5_940
namespace S5_940

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 2 then if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 3 then if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (4 : Fin 5) else if b = 0 then (4 : Fin 5) else if b = 1 then (4 : Fin 5) else if b = 2 then (4 : Fin 5) else if b = 3 then (4 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_940.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.S4_59.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (0 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_940.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_940.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_940.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_940.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_940.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_940.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_940.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_940.table.checkIdentityNat_sound
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
    transferBasis = (firstOccurrenceFourBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_940.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_940.table.semigroup
        (firstOccurrenceFourBasis) :=
    SemigroupBasis.Generated.S4_59.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_940.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_940.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_940
-- END S5_940

end SemigroupBasis.Generated.FirstOccurrenceTransfers

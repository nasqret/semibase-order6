import SemigroupBasis.Generated.Order4RootTransfersLayer1

namespace SemigroupBasis.Generated.Order4RootTransfers

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S5_36
namespace S5_36

def powerEmbedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_29.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_36.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else (3 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else (4 : Fin 5)
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
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw4 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3, transferLaw4]

def transferFiniteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferFiniteLaw4_map :
    transferFiniteLaw4.map Fin.val = transferLaw4 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_36.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)
  · subst e
    rw [← transferFiniteLaw4_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      transferFiniteLaw4 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def targetFiniteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetFiniteLaw4_map :
    targetFiniteLaw4.map Fin.val = targetLaw4 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_36.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)
  · subst e
    rw [← targetFiniteLaw4_map]
    exact SemigroupBasis.Generated.Catalogue.S5_36.table.checkIdentityNat_sound
      targetFiniteLaw4 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst4 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw4.lhs targetLaw4.rhs :=
      Derives.fromBasis (e := targetLaw4) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst4
    simpa [transferLaw4, targetLaw4, bridgeSubst4, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S5_29.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_36.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_36.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S5_29.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S5_29.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_36.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_36
-- END S5_36

-- BEGIN S5_40
namespace S5_40

def powerEmbedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_29.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_40.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else (3 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else (4 : Fin 5)
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
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw4 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3, transferLaw4]

def transferFiniteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferFiniteLaw4_map :
    transferFiniteLaw4.map Fin.val = transferLaw4 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_40.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)
  · subst e
    rw [← transferFiniteLaw4_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      transferFiniteLaw4 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def targetFiniteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetFiniteLaw4_map :
    targetFiniteLaw4.map Fin.val = targetLaw4 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_40.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)
  · subst e
    rw [← targetFiniteLaw4_map]
    exact SemigroupBasis.Generated.Catalogue.S5_40.table.checkIdentityNat_sound
      targetFiniteLaw4 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst4 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw4.lhs targetLaw4.rhs :=
      Derives.fromBasis (e := targetLaw4) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst4
    simpa [transferLaw4, targetLaw4, bridgeSubst4, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S5_29.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_40.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_40.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S5_29.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S5_29.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_40.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_40.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_40
-- END S5_40

-- BEGIN S5_46
namespace S5_46

def powerEmbedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_29.table.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_46.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 5) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (2 : Fin 5) else (3 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (0 : Fin 5) else (4 : Fin 5)
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
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def transferLaw4 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3, transferLaw4]

def transferFiniteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def transferFiniteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferFiniteLaw4_map :
    transferFiniteLaw4.map Fin.val = transferLaw4 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_46.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)
  · subst e
    rw [← transferFiniteLaw4_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      transferFiniteLaw4 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def targetLaw4 : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3, targetLaw4]

def targetFiniteLaw0 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2]⟩⟩

def targetFiniteLaw4 : Identity (Fin 2) :=
  ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetFiniteLaw4_map :
    targetFiniteLaw4.map Fin.val = targetLaw4 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_46.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)
  · subst e
    rw [← targetFiniteLaw4_map]
    exact SemigroupBasis.Generated.Catalogue.S5_46.table.checkIdentityNat_sound
      targetFiniteLaw4 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

def bridgeSubst4 : Nat → Word Nat
  | 0 => Word.singleton 0
  | 1 => Word.singleton 1
  | n + 2 => Word.singleton (n + 2)

theorem transferAxiomsDerive :
    ∀ e : Identity Nat, e ∈ transferBasis →
      Derives targetBasis e.lhs e.rhs := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he
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
  · subst e
    have h : Derives targetBasis targetLaw4.lhs targetLaw4.rhs :=
      Derives.fromBasis (e := targetLaw4) (by simp [targetBasis])
    have renamed := Derives.subst (h) bridgeSubst4
    simpa [transferLaw4, targetLaw4, bridgeSubst4, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S5_29.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_46.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_46.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S5_29.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S5_29.representative_basis.inheritAlongPowerEmbedding powerEmbedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_46.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


end S5_46
-- END S5_46

-- BEGIN S5_292
namespace S5_292

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_57.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_292.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_292.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_292.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_292.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_292.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_292.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_292.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_292.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_292.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_292.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_292.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_292.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_292.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_57.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_292.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_292.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_292
-- END S5_292

-- BEGIN S5_317
namespace S5_317

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_65.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_317.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_317.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_317.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_317.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_317.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_317.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_317.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_317.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_317.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_317.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_317.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_317.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_317.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_65.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_317.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_317.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_317
-- END S5_317

-- BEGIN S5_350
namespace S5_350

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_350.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_350.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_350.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_350.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_350.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_350.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_350.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_350.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_350.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_350.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_350.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_350.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_350.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_350
-- END S5_350

-- BEGIN S5_357
namespace S5_357

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_357.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_357.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_357.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_357.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_357.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_357.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_357.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_357.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_357.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 0
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 2
  | 2 => Word.singleton 0
  | n + 3 => Word.singleton (n + 3)

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
    have renamed := Derives.subst (Derives.symm h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (reversedBasis SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_357.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_357.table.semigroup
        (reversedBasis SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.opposite_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_357.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_357.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_357
-- END S5_357

-- BEGIN S5_405
namespace S5_405

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_405.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_405.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_405.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_405.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_405.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_405.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_405.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_405.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_405.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_405.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_405.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_405.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_405.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_405
-- END S5_405

-- BEGIN S5_409
namespace S5_409

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_409.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_409.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_409.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_409.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_409.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_409.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_409.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_409.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_409.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)

def bridgeSubst0 : Nat → Word Nat
  | 0 => Word.singleton 0
  | n + 1 => Word.singleton (n + 1)

def bridgeSubst1 : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 0
  | n + 2 => Word.singleton (n + 2)

def bridgeSubst2 : Nat → Word Nat
  | 0 => Word.singleton 1
  | 1 => Word.singleton 2
  | 2 => Word.singleton 0
  | n + 3 => Word.singleton (n + 3)

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
    have renamed := Derives.subst (Derives.symm h) bridgeSubst2
    simpa [transferLaw2, targetLaw2, bridgeSubst2, Word.bind, Word.singleton, Word.append] using renamed

theorem transferBasis_eq_source :
    transferBasis = (reversedBasis SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_409.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_409.table.semigroup
        (reversedBasis SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.opposite_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_409.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_409.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_409
-- END S5_409

-- BEGIN S5_412
namespace S5_412

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (0 : Fin 5) else (0 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (1 : Fin 5) else (1 : Fin 5) else if a = 2 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (0 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 3 then if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (1 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if b = 0 then (0 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (4 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_412.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 4) else if a = 1 then (1 : Fin 4) else if a = 2 then (1 : Fin 4) else if a = 3 then (2 : Fin 4) else (3 : Fin 4)
  map_mul := by decide
  preimage := fun b : Fin 4 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (1 : Fin 5) else if b = 2 then (3 : Fin 5) else (4 : Fin 5)
  right_inverse := by
    intro b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_412.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_412.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_412.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_412.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_412.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_412.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_412.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_412.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_412.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_412.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_412.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_412.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_412
-- END S5_412

-- BEGIN S5_414
namespace S5_414

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_414.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_414.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_414.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_414.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_414.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_414.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_414.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_414.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_414.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_414.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_414.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_414.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_414.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_414
-- END S5_414

-- BEGIN S5_420
namespace S5_420

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_82.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_420.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_420.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_420.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_420.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_420.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_420.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_420.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_420.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_420.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_420.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_420.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_420.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_420.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_82.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_420.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_420.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_420
-- END S5_420

-- BEGIN S5_428
namespace S5_428

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_85.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_428.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_428.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_428.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_428.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_428.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_428.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_428.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_428.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_428.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_428.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_428.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_428.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_428.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_85.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_428.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_428.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_428
-- END S5_428

-- BEGIN S5_547
namespace S5_547

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_57.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_547.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_547.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_547.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_547.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_547.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_547.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_547.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_547.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_547.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_547.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_547.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_547.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_547.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_57.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_547.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_547.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_547
-- END S5_547

-- BEGIN S5_597
namespace S5_597

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_65.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_597.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_597.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_597.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_597.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_597.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_597.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_597.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_597.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_597.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_597.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_597.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_597.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_597.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_65.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_597.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_597.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_597
-- END S5_597

-- BEGIN S5_641
namespace S5_641

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_641.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_641.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_641.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_641.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_641.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_641.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_641.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_641.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_641.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_641.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_641.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_641.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_641.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_641
-- END S5_641

-- BEGIN S5_650
namespace S5_650

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_82.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_650.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_650.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_650.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_650.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_650.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_650.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_650.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_650.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_650.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_650.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_650.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_650.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_650.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_82.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_650.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_650.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_650
-- END S5_650

-- BEGIN S5_677
namespace S5_677

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_57.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_677.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_677.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_677.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_677.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_677.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_677.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_677.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_677.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_677.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_677.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_677.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_677.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_677.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_57.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_677.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_677.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_677
-- END S5_677

-- BEGIN S5_703
namespace S5_703

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_57.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_703.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_703.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_703.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_703.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_703.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_703.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_703.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_703.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_703.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_703.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_703.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_703.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_703.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_57.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_703.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_703.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_703
-- END S5_703

-- BEGIN S5_706
namespace S5_706

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_57.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_706.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_706.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_706.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_706.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_706.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_706.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_706.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_706.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_706.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_706.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_706.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_706.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_706.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_57.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_706.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_706.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_706
-- END S5_706

-- BEGIN S5_709
namespace S5_709

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_57.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_709.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_709.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_709.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_709.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_709.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_709.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_709.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_709.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_709.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_709.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_709.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_709.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_709.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_57.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_709.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_709.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_709
-- END S5_709

-- BEGIN S5_749
namespace S5_749

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_65.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_749.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_749.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_749.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_749.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_749.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_749.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_749.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_749.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_749.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_749.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_749.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_749.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_749.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_65.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_749.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_749.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_749
-- END S5_749

-- BEGIN S5_750
namespace S5_750

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_65.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_750.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_750.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_750.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_750.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_750.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_750.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_750.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_750.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_750.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_750.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_750.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_750.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_750.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_65.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_750.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_750.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_750
-- END S5_750

-- BEGIN S5_751
namespace S5_751

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_65.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_751.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_751.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_751.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_751.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_751.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_751.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_751.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_751.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_751.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_751.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_751.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_751.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_751.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_65.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_751.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_751.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_751
-- END S5_751

-- BEGIN S5_752
namespace S5_752

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_65.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_752.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_752.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_752.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_752.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_752.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_752.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_752.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_752.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_752.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_752.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_752.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_752.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_752.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_65.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_752.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_752.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_752
-- END S5_752

-- BEGIN S5_836
namespace S5_836

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_836.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_836.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_836.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_836.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_836.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_836.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_836.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_836.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_836.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_836.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_836.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_836.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_836.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_836
-- END S5_836

-- BEGIN S5_839
namespace S5_839

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_839.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_839.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_839.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_839.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_839.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_839.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_839.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_839.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_839.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_839.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_839.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_839.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_839.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_839
-- END S5_839

-- BEGIN S5_875
namespace S5_875

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_875.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_875.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_875.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_875.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_875.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_875.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_875.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_875.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_875.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_875.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_875.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_875.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_875.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_875
-- END S5_875

-- BEGIN S5_877
namespace S5_877

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_877.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_877.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_877.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_877.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_877.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_877.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_877.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_877.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_877.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_877.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_877.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_877.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_877.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_877
-- END S5_877

-- BEGIN S5_879
namespace S5_879

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_879.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_879.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_879.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_879.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_879.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_879.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_879.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_879.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_879.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_879.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_879.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_879.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_879.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_879
-- END S5_879

-- BEGIN S5_884
namespace S5_884

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_57.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_884.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_884.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_884.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_884.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_884.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_884.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_884.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_884.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_884.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_884.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_884.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_884.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_884.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_57.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_884.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_884.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_884
-- END S5_884

-- BEGIN S5_892
namespace S5_892

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_65.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_892.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_892.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_892.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_892.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_892.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_892.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_892.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_892.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_892.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_892.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_892.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_892.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_892.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_65.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_65.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_892.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_892.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_892
-- END S5_892

-- BEGIN S5_893
namespace S5_893

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_82.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_893.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_893.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_893.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_893.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_893.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_893.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_893.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_893.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_893.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_893.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_893.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_893.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_893.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_82.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_893.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_893.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_893
-- END S5_893

-- BEGIN S5_906
namespace S5_906

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_79.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_906.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def transferLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_906.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_906.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_906.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_906.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw2 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_906.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_906.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_906.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_906.table.checkIdentityNat_sound
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
  | 2 => Word.singleton 2
  | n + 3 => Word.singleton (n + 3)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_906.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_906.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_79.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_79.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_906.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_906.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_906
-- END S5_906

-- BEGIN S5_908
namespace S5_908

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_85.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_908.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_908.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_908.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_908.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_908.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_908.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_908.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_908.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_908.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_908.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_908.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_908.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_908.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_85.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_908.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_908.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_908
-- END S5_908

-- BEGIN S5_915
namespace S5_915

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_82.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_915.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_915.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_915.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_915.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_915.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_915.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_915.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_915.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_915.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_915.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_915.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_915.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_915.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_82.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_915.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_915.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_915
-- END S5_915

-- BEGIN S5_916
namespace S5_916

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_82.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_916.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_916.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_916.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_916.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_916.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_916.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_916.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_916.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_916.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_916.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_916.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_916.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_916.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_82.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_916.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_916.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_916
-- END S5_916

-- BEGIN S5_918
namespace S5_918

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_85.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_918.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_918.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_918.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_918.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_918.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_918.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_918.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_918.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_918.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_918.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_918.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_918.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_918.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_85.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_918.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_918.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_918
-- END S5_918

-- BEGIN S5_930
namespace S5_930

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_82.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_930.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_930.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_930.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_930.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_930.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_930.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_930.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_930.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_930.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_930.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_930.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_930.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_930.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_82.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_82.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_930.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_930.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_930
-- END S5_930

-- BEGIN S5_937
namespace S5_937

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_85.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_937.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_937.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_937.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_937.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_937.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_937.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_937.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_937.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_937.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_937.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_937.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_937.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_937.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_85.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_937.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_937.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_937
-- END S5_937

-- BEGIN S5_939
namespace S5_939

def subMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 1 then if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 2 then if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (2 : Fin 5) else (2 : Fin 5) else if a = 3 then if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (3 : Fin 5) else (3 : Fin 5) else if b = 0 then (2 : Fin 5) else if b = 1 then (2 : Fin 5) else if b = 2 then (2 : Fin 5) else if b = 3 then (4 : Fin 5) else (4 : Fin 5)

def subTable : FiniteTable where
  order := 5
  mul := subMul
  assoc := by decide

def subEmbedding :
    Embedding subTable.semigroup SemigroupBasis.Generated.Catalogue.S5_939.table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  injective := by
    intro a b
    exact by decide +revert

def quotient :
    SplitSurjection subTable.semigroup
      SemigroupBasis.Generated.Catalogue.S4_57.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_939.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_939.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_939.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_939.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_939.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_939.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_939.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_939.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_939.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_939.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_939.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_939.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_57.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_57.representative_basis.inheritAlongSubsemigroupQuotient subEmbedding quotient (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_939.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_939.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_939
-- END S5_939

-- BEGIN S5_941
namespace S5_941

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_85.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_941.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_941.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_941.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_941.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_941.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_941.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_941.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_941.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_941.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_941.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_941.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_941.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_941.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_85.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_941.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_941.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_941
-- END S5_941

-- BEGIN S5_942
namespace S5_942

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_85.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_942.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_942.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_942.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_942.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_942.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_942.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_942.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_942.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_942.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_942.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_942.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_942.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_942.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_85.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_942.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_942.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_942
-- END S5_942

-- BEGIN S5_946
namespace S5_946

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_85.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_946.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_946.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_946.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_946.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_946.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_946.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_946.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_946.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_946.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_946.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_946.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_946.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_946.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_85.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_946.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_946.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_946
-- END S5_946

-- BEGIN S5_949
namespace S5_949

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_85.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_949.table.semigroup where
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

def transferLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def transferBasis : List (Identity Nat) :=
  [transferLaw0, transferLaw1, transferLaw2, transferLaw3]

def transferFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def transferFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def transferFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def transferFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem transferFiniteLaw0_map :
    transferFiniteLaw0.map Fin.val = transferLaw0 := rfl

theorem transferFiniteLaw1_map :
    transferFiniteLaw1.map Fin.val = transferLaw1 := rfl

theorem transferFiniteLaw2_map :
    transferFiniteLaw2.map Fin.val = transferLaw2 := rfl

theorem transferFiniteLaw3_map :
    transferFiniteLaw3.map Fin.val = transferLaw3 := rfl

theorem transferModels :
    Models SemigroupBasis.Generated.Catalogue.S5_949.table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← transferFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_949.table.checkIdentityNat_sound
      transferFiniteLaw0 (by decide)
  · subst e
    rw [← transferFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_949.table.checkIdentityNat_sound
      transferFiniteLaw1 (by decide)
  · subst e
    rw [← transferFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_949.table.checkIdentityNat_sound
      transferFiniteLaw2 (by decide)
  · subst e
    rw [← transferFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_949.table.checkIdentityNat_sound
      transferFiniteLaw3 (by decide)

def targetLaw0 : Identity Nat :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetLaw1 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetLaw2 : Identity Nat :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetLaw3 : Identity Nat :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

def targetBasis : List (Identity Nat) :=
  [targetLaw0, targetLaw1, targetLaw2, targetLaw3]

def targetFiniteLaw0 : Identity (Fin 1) :=
  ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩

def targetFiniteLaw1 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [0, 1]⟩⟩

def targetFiniteLaw2 : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨0, [1, 0]⟩⟩

def targetFiniteLaw3 : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [2, 1]⟩⟩

theorem targetFiniteLaw0_map :
    targetFiniteLaw0.map Fin.val = targetLaw0 := rfl

theorem targetFiniteLaw1_map :
    targetFiniteLaw1.map Fin.val = targetLaw1 := rfl

theorem targetFiniteLaw2_map :
    targetFiniteLaw2.map Fin.val = targetLaw2 := rfl

theorem targetFiniteLaw3_map :
    targetFiniteLaw3.map Fin.val = targetLaw3 := rfl

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_949.table.semigroup targetBasis := by
  intro e he
  simp only [targetBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he
  · subst e
    rw [← targetFiniteLaw0_map]
    exact SemigroupBasis.Generated.Catalogue.S5_949.table.checkIdentityNat_sound
      targetFiniteLaw0 (by decide)
  · subst e
    rw [← targetFiniteLaw1_map]
    exact SemigroupBasis.Generated.Catalogue.S5_949.table.checkIdentityNat_sound
      targetFiniteLaw1 (by decide)
  · subst e
    rw [← targetFiniteLaw2_map]
    exact SemigroupBasis.Generated.Catalogue.S5_949.table.checkIdentityNat_sound
      targetFiniteLaw2 (by decide)
  · subst e
    rw [← targetFiniteLaw3_map]
    exact SemigroupBasis.Generated.Catalogue.S5_949.table.checkIdentityNat_sound
      targetFiniteLaw3 (by decide)

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
    transferBasis = (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) := rfl

theorem transferred_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_949.table.semigroup transferBasis := by
  have inherited :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_949.table.semigroup
        (SemigroupBasis.Generated.Order4RootTransfers.S4_85.targetBasis) :=
    SemigroupBasis.Generated.Order4RootTransfers.S4_85.representative_basis.inheritAlongEmbedding embedding (by simpa only [transferBasis_eq_source] using transferModels)
  simpa only [transferBasis_eq_source] using inherited

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_949.table.semigroup targetBasis :=
  transferred_basis.replace targetModels transferAxiomsDerive


theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_949.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  representative_basis.oppositeReversed

end S5_949
-- END S5_949

end SemigroupBasis.Generated.Order4RootTransfers

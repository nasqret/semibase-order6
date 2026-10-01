import SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets
import SemigroupBasis.FiniteReflection
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeComponentFive

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

def law0 : Identity Nat := Identity.mk (w 0 [0, 0]) (w 0 [0, 0, 0])
def law1 : Identity Nat := Identity.mk (w 0 [0, 0, 1]) (w 0 [0, 1])
def law2 : Identity Nat := Identity.mk (w 0 [0, 1]) (w 0 [0, 1, 1])
def law3 : Identity Nat := Identity.mk (w 0 [0, 1]) (w 0 [1, 0])
def law4 : Identity Nat := Identity.mk (w 0 [1, 1]) (w 0 [1, 1, 1])
def law5 : Identity Nat := Identity.mk (w 0 [1, 1, 2]) (w 0 [1, 2])
def law6 : Identity Nat := Identity.mk (w 0 [1, 2]) (w 0 [2, 1])

def transferBasis : List (Identity Nat) :=
  [law0, law1, law2, law3, law4, law5, law6]

theorem transferBasis_eq_shared : transferBasis = SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis := by
  rfl

def finiteLaw0 : Identity (Fin 1) :=
  Identity.mk (Word.mk 0 [0, 0]) (Word.mk 0 [0, 0, 0])
def finiteLaw1 : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 0, 1]) (Word.mk 0 [0, 1])
def finiteLaw2 : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 1]) (Word.mk 0 [0, 1, 1])
def finiteLaw3 : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [0, 1]) (Word.mk 0 [1, 0])
def finiteLaw4 : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [1, 1]) (Word.mk 0 [1, 1, 1])
def finiteLaw5 : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 1, 2]) (Word.mk 0 [1, 2])
def finiteLaw6 : Identity (Fin 3) :=
  Identity.mk (Word.mk 0 [1, 2]) (Word.mk 0 [2, 1])

theorem finiteLaw0_map : finiteLaw0.map Fin.val = law0 := by decide
theorem finiteLaw1_map : finiteLaw1.map Fin.val = law1 := by decide
theorem finiteLaw2_map : finiteLaw2.map Fin.val = law2 := by decide
theorem finiteLaw3_map : finiteLaw3.map Fin.val = law3 := by decide
theorem finiteLaw4_map : finiteLaw4.map Fin.val = law4 := by decide
theorem finiteLaw5_map : finiteLaw5.map Fin.val = law5 := by decide
theorem finiteLaw6_map : finiteLaw6.map Fin.val = law6 := by decide

namespace S6_5560

/-- Authenticated order-six table, SHA-256 `1d1d1a98ca807201926cf0bb5879ea29e1aee2b332d548aae9d3c287b7958790`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "1d1d1a98ca807201926cf0bb5879ea29e1aee2b332d548aae9d3c287b7958790"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2], [0, 0, 0, 1, 0, 2], [4, 4, 4, 4, 4, 4], [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def recordedCoordinatesZeroBased : List (List Nat) := [[0,0,2,0,0,5],[0,1,0,3,4,0]]

theorem recordedCoordinatesZeroBased_certificate :
    recordedCoordinatesZeroBased = [[0,0,2,0,0,5],[0,1,0,3,4,0]] := by decide

def coordinateValue (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 2) :
    Hom SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5550.table.semigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5550.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

theorem targetModelsTransfer : Models table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he
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

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis

theorem targetModels : Models table.semigroup basis := by
  change Models table.semigroup transferBasis
  exact targetModelsTransfer

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5550.representative_basis.inheritAlongPowerEmbedding
    sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5560

namespace S6_5564

/-- Authenticated order-six table, SHA-256 `6f2869a5f5708ddef47308e725ec21136572e1293894610025312c5c27a5b237`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "6f2869a5f5708ddef47308e725ec21136572e1293894610025312c5c27a5b237"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2], [0, 0, 0, 1, 0, 2], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def recordedCoordinatesZeroBased : List (List Nat) := [[0,0,2,0,4,5],[0,1,0,3,0,0]]

theorem recordedCoordinatesZeroBased_certificate :
    recordedCoordinatesZeroBased = [[0,0,2,0,4,5],[0,1,0,3,0,0]] := by decide

def coordinateValue (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 2) :
    Hom SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5554.table.semigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5554.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

theorem targetModelsTransfer : Models table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he
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

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis

theorem targetModels : Models table.semigroup basis := by
  change Models table.semigroup transferBasis
  exact targetModelsTransfer

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5554.representative_basis.inheritAlongPowerEmbedding
    sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5564

namespace S6_9544

/-- Authenticated order-six table, SHA-256 `f4bc557b91859b16c106707381d7cb459ff58037a6c816f9839fd3b942294615`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "f4bc557b91859b16c106707381d7cb459ff58037a6c816f9839fd3b942294615"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 4], [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS2_4Map (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (1 : Fin 2) else (0 : Fin 2)

def ontoS2_4Section (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def ontoS2_4 : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoS2_4Map
  map_mul := by decide
  preimage := ontoS2_4Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_196OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)

def ontoS5_196OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoS5_196Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite where
  toFun := ontoS5_196OppositeMap
  map_mul := by decide
  preimage := ontoS5_196OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite where
  left := ontoS2_4
  right := ontoS5_196Opposite
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9544

namespace S6_9547

/-- Authenticated order-six table, SHA-256 `99732c6d918a41c03158a3f5fd248bcfda895327498532f7ceb8d0b3d2271a63`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "99732c6d918a41c03158a3f5fd248bcfda895327498532f7ceb8d0b3d2271a63"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 4], [3, 3, 3, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS2_4Map (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (1 : Fin 2) else (1 : Fin 2)

def ontoS2_4Section (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def ontoS2_4 : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoS2_4Map
  map_mul := by decide
  preimage := ontoS2_4Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_196OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)

def ontoS5_196OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoS5_196Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite where
  toFun := ontoS5_196OppositeMap
  map_mul := by decide
  preimage := ontoS5_196OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite where
  left := ontoS2_4
  right := ontoS5_196Opposite
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9547

namespace S6_9633

/-- Authenticated order-six table, SHA-256 `d7a69d06efcb1230d7d7611414b0225eb74ff1110cd1aa97d7cdfea9266dd6c5`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "d7a69d06efcb1230d7d7611414b0225eb74ff1110cd1aa97d7cdfea9266dd6c5"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 3, 3, 3], [0, 0, 0, 3, 3, 3], [0, 0, 1, 3, 3, 3], [3, 3, 3, 3, 3, 3], [4, 4, 4, 3, 3, 3], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def recordedCoordinatesZeroBased : List (List Nat) := [[0,1,0,2,0,0],[3,3,4,3,5,0]]

theorem recordedCoordinatesZeroBased_certificate :
    recordedCoordinatesZeroBased = [[0,1,0,2,0,0],[3,3,4,3,5,0]] := by decide

def coordinateValue (i : Fin 2) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 2) :
    Hom SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5550.table.semigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5550.table.semigroup (table.semigroup.pi (Fin 2)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

theorem targetModelsTransfer : Models table.semigroup transferBasis := by
  intro e he
  simp only [transferBasis, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he
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

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis

theorem targetModels : Models table.semigroup basis := by
  change Models table.semigroup transferBasis
  exact targetModelsTransfer

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets.S6_5550.representative_basis.inheritAlongPowerEmbedding
    sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9633

end SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeComponentFive

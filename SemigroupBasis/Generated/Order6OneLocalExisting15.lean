import SemigroupBasis.Generated.Order6FactorPairS2S5378Targets
import SemigroupBasis.Generated.Order6FactorPairS2S5400Targets
import SemigroupBasis.Generated.Order6FactorPairS3_11Targets
import SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma

set_option maxRecDepth 100000

/-!
# Unconditional one-local existing-proof endpoints

Twelve DAG roots and their fifteen exact leaves are covered by six
previously proved factor intersections.  No conditional reach-plan
theorem is used by this module.
-/

namespace SemigroupBasis.Generated.Order6OneLocalExisting15

namespace S6_11230

abbrev table := SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_11230.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_11230.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_11230.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11230

namespace S6_11521

/-- Authenticated order-six table, SHA-256 `7874b43f7b7198a1f5d7fa72c23e42577598262801f2320de46a4f17d753815e`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "7874b43f7b7198a1f5d7fa72c23e42577598262801f2320de46a4f17d753815e"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 1], [0, 1, 2, 3, 4, 5], [0, 1, 3, 2, 4, 5], [0, 1, 4, 4, 4, 0], [0, 0, 5, 5, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (1 : Fin 3) else if a = 4 then (2 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (2 : Fin 6) else if a = 1 then (3 : Fin 6) else (0 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (4 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (2 : Fin 5) else (3 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else (2 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S5_840.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev directBasis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem directBasis_eq_existing :
    directBasis = SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal.basis := by decide

private theorem direct_endpoint :
    BasisFor table.semigroup directBasis := by
  rw [directBasis_eq_existing]
  exact SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.intersectionBasisS5_840.basisFor pair

/-- Unconditional representative endpoint. -/
theorem representative_basis :
    BasisFor table.semigroup basis :=
  direct_endpoint

end S6_11521

namespace S6_4076

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4076.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_4f48d5dc7526fb97.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4076.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4076.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4076

namespace S6_4089

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4089.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4089.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4089.representative_basis

end S6_4089

namespace S6_4185

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4185.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_4f48d5dc7526fb97.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4185.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4185.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4185

namespace S6_4187

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4187.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_4f48d5dc7526fb97.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4187.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4187.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4187

namespace S6_4199

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4199.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4199.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4199.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4199

namespace S6_4286

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4286.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_4f48d5dc7526fb97.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4286.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5378Targets.S6_4286.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_4286

namespace S6_4295

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4295.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4295.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_4295.representative_basis

end S6_4295

namespace S6_6369

abbrev table := SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_6369.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_4f48d5dc7526fb97.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_6369.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_6369.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_6369

namespace S6_6462

/-- Authenticated order-six table, SHA-256 `a7e8f0ffb83981e3081fe390a53beda17650d8c571b91751f6c2070dc6a2c940`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (0 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a7e8f0ffb83981e3081fe390a53beda17650d8c571b91751f6c2070dc6a2c940"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 2, 2, 0], [0, 1, 2, 3, 4, 0], [0, 1, 2, 4, 3, 0], [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (1 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (4 : Fin 5) else (3 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (5 : Fin 6) else (3 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup.opposite SemigroupBasis.Generated.Catalogue.S5_378.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup.opposite SemigroupBasis.Generated.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S5_378.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev directBasis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_4f48d5dc7526fb97.basis
abbrev basis : List (Identity Nat) := (reversedBasis SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_4f48d5dc7526fb97.basis)

private theorem directBasis_eq_existing :
    directBasis = SemigroupBasis.CoRoots.Order6FactorPairS2S5378.basis := by decide

private theorem direct_endpoint :
    BasisFor table.semigroup.opposite directBasis := by
  rw [directBasis_eq_existing]
  exact SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.intersectionBasisS5_378.basisFor pair

/-- The direct factor pair is on the opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) := by
  simpa [basis, directBasis, reversedBasis_reversedBasis] using
    direct_endpoint

/-- Unconditional representative endpoint with reversed Sigma. -/
theorem representative_basis :
    BasisFor table.semigroup basis := by
  simpa [basis, directBasis] using direct_endpoint.oppositeReversed

end S6_6462

namespace S6_6471

abbrev table := SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_6471.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_6471.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS3_11Targets.S6_6471.representative_basis

end S6_6471

namespace S6_6550

/-- Authenticated order-six table, SHA-256 `59e8f53fd39dd659eb471e1abec7557ad0fb395795cfefdd710f624af9ce3fe9`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "59e8f53fd39dd659eb471e1abec7557ad0fb395795cfefdd710f624af9ce3fe9"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0], [0, 0, 0, 2, 2, 2], [0, 1, 2, 3, 4, 5], [0, 1, 2, 4, 3, 5], [0, 1, 0, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS3Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (2 : Fin 3) else if a = 1 then (2 : Fin 3) else if a = 2 then (2 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoS3Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (3 : Fin 6) else if a = 1 then (4 : Fin 6) else (0 : Fin 6)

def ontoS3 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := ontoS3Map
  map_mul := by decide
  preimage := ontoS3Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (4 : Fin 5) else (3 : Fin 5)

def ontoS5Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (5 : Fin 6) else (3 : Fin 6)

def ontoS5 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup where
  toFun := ontoS5Map
  map_mul := by decide
  preimage := ontoS5Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup SemigroupBasis.Generated.Catalogue.S5_400.table.semigroup where
  left := ontoS3
  right := ontoS5
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev directBasis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem directBasis_eq_existing :
    directBasis = SemigroupBasis.CoRoots.Order6FactorPairS2S5400Normal.basis := by decide

private theorem direct_endpoint :
    BasisFor table.semigroup directBasis := by
  rw [directBasis_eq_existing]
  exact SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.intersectionBasisS5_400.basisFor pair

/-- Unconditional representative endpoint. -/
theorem representative_basis :
    BasisFor table.semigroup basis :=
  direct_endpoint

end S6_6550

namespace S6_8873

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_8873.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_8873.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_8873.representative_basis

end S6_8873

namespace S6_9017

abbrev table := SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_9017.table
abbrev basis : List (Identity Nat) := SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_01f008d64c8bdb44.basis

private theorem basis_eq_source :
    basis = SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_9017.basis := by decide

/-- Unconditional endpoint from the existing factor intersection. -/
theorem representative_basis : BasisFor table.semigroup basis := by
  rw [basis_eq_source]
  exact SemigroupBasis.Generated.Order6FactorPairS2S5400Targets.S6_9017.representative_basis

end S6_9017

end SemigroupBasis.Generated.Order6OneLocalExisting15

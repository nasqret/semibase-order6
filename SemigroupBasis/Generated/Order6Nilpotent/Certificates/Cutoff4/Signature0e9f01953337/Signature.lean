/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337
import SemigroupBasis.FiniteNilpotentLongCollapse
import SemigroupBasis.FiniteNilpotentDecisionDAG
import SemigroupBasis.FiniteNilpotentCounterexample

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337

open SemigroupBasis

abbrev basis := SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.representativeBasis
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.representativeInventoryIdentities
abbrev common := SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.representativeCommon

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basis_eq :
    basis =
      [
        ⟨⟨1, [0, 0]⟩, ⟨0, [1, 0]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨1, [0, 1]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨0, [1, 1]⟩⟩,
        ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩,
        ⟨⟨2, [1, 0]⟩, ⟨1, [2, 0]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨7, [6, 5, 4]⟩⟩
      ] := by
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem inventory_eq :
    inventory =
      [
        ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨0, [1, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [0, 0]⟩⟩,
        ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩,
        ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩
      ] := by
  decide

theorem inventoryIdentity000RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity001RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨0, [1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨0, [1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity002RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity003RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity004RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryRestrictedGrowth :
    FiniteCertificate.AllRestrictedGrowth inventory := by
  rw [inventory_eq]
  exact
    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity000RestrictedGrowth <|
      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity001RestrictedGrowth <|
        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity002RestrictedGrowth <|
          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity003RestrictedGrowth <|
            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity004RestrictedGrowth <|
              FiniteNilpotentCounterexample.allRestrictedGrowth_nil

def derivationRoots :
    List SemigroupBasis.FiniteNilpotentDecisionDAG.Root :=
  [
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [0, 1]⟩⟩
        basisIndex := 0
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨0, [1, 0]⟩⟩
        basisIndex := 1
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [0, 0]⟩⟩
        basisIndex := 2
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 0]⟩, ⟨1, [0, 1]⟩⟩
        basisIndex := 3
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [1, 2]⟩, ⟨1, [0, 2]⟩⟩
        basisIndex := 4
        symmetry := false
        mapping := [2, 1, 0]
      }
  ]

theorem listed : FiniteCertificate.DerivesAll basis inventory :=
  SemigroupBasis.FiniteNilpotentDecisionDAG.check_sound
    (basis := basis) (identities := inventory)
    (roots := derivationRoots) (by decide)

theorem toCommon :
    forall word : Word Nat,
      4 <= word.toList.length -> Derives basis word common :=
  SemigroupBasis.FiniteNilpotentLongCollapse.toCommon_of_check
    (by decide)

def certificate : SemigroupBasis.Generated.Order6Nilpotent.Signature0e9f01953337.SignatureCertificate where
  toCommon := toCommon
  listed := listed

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0e9f01953337

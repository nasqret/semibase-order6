/- Materialized from the pinned order-six nilpotent inventories.
   WMI compilation and release replay remain mandatory. -/
import SemigroupBasis.Generated.Order6Nilpotent.Signature0f62c5e540ab
import SemigroupBasis.FiniteNilpotentLongCollapse
import SemigroupBasis.FiniteNilpotentDecisionDAG
import SemigroupBasis.FiniteNilpotentCounterexample

namespace SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0f62c5e540ab

open SemigroupBasis

abbrev basis := SemigroupBasis.Generated.Order6Nilpotent.Signature0f62c5e540ab.representativeBasis
abbrev inventory := SemigroupBasis.Generated.Order6Nilpotent.Signature0f62c5e540ab.representativeInventoryIdentities
abbrev common := SemigroupBasis.Generated.Order6Nilpotent.Signature0f62c5e540ab.representativeCommon

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem basis_eq :
    basis =
      [
        ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [0, 0]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [1, 0]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨0, [1, 1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [1, 1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨2, [1, 1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨2, [2, 1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨4, [3, 2, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨2, [1, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨2, [2, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨4, [3, 2, 1]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨2, [0, 0]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨1, [1, 0]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨2, [2, 0]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨0, [1, 1]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨2, [1, 1]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨2, [2, 1]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨0, [0, 2]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨1, [1, 2]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨1, [2, 2]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨3, [2, 2]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨3, [3, 2]⟩⟩,
        ⟨⟨1, [0, 0]⟩, ⟨5, [4, 3, 2]⟩⟩,
        ⟨⟨1, [1, 0]⟩, ⟨2, [2, 0]⟩⟩,
        ⟨⟨1, [1, 0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨1, [1, 0]⟩, ⟨2, [2, 1]⟩⟩,
        ⟨⟨1, [1, 0]⟩, ⟨1, [1, 2]⟩⟩,
        ⟨⟨1, [1, 0]⟩, ⟨3, [3, 2]⟩⟩,
        ⟨⟨1, [1, 0]⟩, ⟨5, [4, 3, 2]⟩⟩,
        ⟨⟨2, [1, 0]⟩, ⟨0, [1, 2]⟩⟩,
        ⟨⟨3, [2, 1, 0]⟩, ⟨7, [6, 5, 4]⟩⟩
      ] := by
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem inventory_eq :
    inventory =
      [
        ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [0, 0]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [1, 0]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨0, [1, 1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [1, 1]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [2, 2]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [1, 2]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [2, 2]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [1, 2]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [1, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨0, [0, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [2, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [1, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [0, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [0, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [2, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [1, 2]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨0, [0, 2]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨0, [2, 2]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [3, 3]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [2, 3]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [2, 1]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨1, [1, 0]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [2, 0]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨0, [0, 2]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [2, 3]⟩⟩,
        ⟨⟨0, [1, 2]⟩, ⟨2, [1, 0]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [2, 3, 0]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [2, 0, 3]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [0, 2, 3]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨0, [1, 2, 3]⟩⟩,
        ⟨⟨0, [0]⟩, ⟨1, [2, 3, 4]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [2, 3, 0]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [2, 0, 3]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [0, 2, 3]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2, 3]⟩⟩,
        ⟨⟨0, [0, 0]⟩, ⟨1, [2, 3, 4]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [3, 0, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [0, 3, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨0, [2, 3, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 1]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [3, 1, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [1, 3, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [2, 3, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 0]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [0, 1, 3]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨0, [2, 1, 3]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [3, 1, 4]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [1, 0, 3]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [2, 0, 3]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [3, 0, 4]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨0, [1, 2, 3]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [1, 3, 4]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [0, 2, 3]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [0, 3, 4]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨1, [2, 3, 4]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨0, [2, 3, 4]⟩⟩,
        ⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 5]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [3, 0, 1]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [0, 3, 1]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨0, [2, 3, 1]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 1]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [3, 1, 0]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [1, 3, 0]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨1, [2, 3, 0]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 0]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [0, 1, 3]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨0, [2, 1, 3]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [3, 1, 4]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [1, 0, 3]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨1, [2, 0, 3]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [3, 0, 4]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨0, [1, 2, 3]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [1, 3, 4]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨1, [0, 2, 3]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [0, 3, 4]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨1, [2, 3, 4]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨0, [2, 3, 4]⟩⟩,
        ⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 5]⟩⟩
      ] := by
  decide

theorem inventoryIdentity000RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨1, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 1)))))⟩

theorem inventoryIdentity001RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2)))))⟩

theorem inventoryIdentity002RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2)))))⟩

theorem inventoryIdentity003RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2)))))⟩

theorem inventoryIdentity004RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))⟩

theorem inventoryIdentity005RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2)))))⟩

theorem inventoryIdentity006RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2)))))⟩

theorem inventoryIdentity007RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [2, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [2, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3)))))⟩

theorem inventoryIdentity008RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3)))))⟩

theorem inventoryIdentity009RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity010RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity011RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity012RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity013RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity014RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [2, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [2, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity015RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity016RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [1, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity017RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨0, [0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity018RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity019RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity020RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity021RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [0, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [0, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity022RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity023RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [1, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity024RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨0, [0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨0, [0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity025RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨0, [2, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨0, [2, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity026RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [3, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [3, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))⟩

theorem inventoryIdentity027RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))⟩

theorem inventoryIdentity028RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [2, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity029RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨1, [1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨2, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 2))))))⟩

theorem inventoryIdentity030RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [2, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [2, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity031RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨0, [0, 2]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨0, [0, 2]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity032RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))⟩

theorem inventoryIdentity033RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 2]⟩, ⟨2, [1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 2]⟩, ⟨2, [1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨3, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 3))))))⟩

theorem inventoryIdentity034RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [2, 3, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [2, 3, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))⟩

theorem inventoryIdentity035RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [2, 0, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [2, 0, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))⟩

theorem inventoryIdentity036RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))⟩

theorem inventoryIdentity037RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨0, [1, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨0, [1, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4))))))⟩

theorem inventoryIdentity038RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0]⟩, ⟨1, [2, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0]⟩, ⟨1, [2, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5))))))⟩

theorem inventoryIdentity039RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [2, 3, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [2, 3, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity040RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [2, 0, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [2, 0, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity041RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity042RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨0, [1, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨0, [1, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity043RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 0]⟩, ⟨1, [2, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 0]⟩, ⟨1, [2, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity044RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [3, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [3, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity045RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [0, 3, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [0, 3, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity046RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨0, [2, 3, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨0, [2, 3, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity047RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity048RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [3, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [3, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity049RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [1, 3, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [1, 3, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity050RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [2, 3, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [2, 3, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity051RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity052RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [0, 1, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [0, 1, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity053RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨0, [2, 1, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨0, [2, 1, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity054RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [3, 1, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [3, 1, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity055RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [1, 0, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [1, 0, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity056RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [2, 0, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [2, 0, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity057RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [3, 0, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [3, 0, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity058RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨0, [1, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨0, [1, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity059RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [1, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [1, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity060RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity061RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [0, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [0, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity062RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨1, [2, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨1, [2, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity063RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨0, [2, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨0, [2, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity064RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 5]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 5]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨6, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 6)))))))⟩

theorem inventoryIdentity065RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [3, 0, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [3, 0, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity066RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [0, 3, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [0, 3, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity067RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨0, [2, 3, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨0, [2, 3, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity068RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 1]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 1]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity069RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [3, 1, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [3, 1, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity070RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [1, 3, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [1, 3, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity071RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨1, [2, 3, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨1, [2, 3, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity072RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 0]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 0]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity073RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [0, 1, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [0, 1, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity074RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨0, [2, 1, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨0, [2, 1, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity075RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [3, 1, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [3, 1, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity076RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [1, 0, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [1, 0, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity077RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨1, [2, 0, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨1, [2, 0, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity078RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [3, 0, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [3, 0, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity079RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨0, [1, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨0, [1, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity080RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [1, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [1, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity081RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨1, [0, 2, 3]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨4, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 4)))))))⟩

theorem inventoryIdentity082RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [0, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [0, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity083RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨1, [2, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨1, [2, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity084RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨0, [2, 3, 4]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨0, [2, 3, 4]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨5, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 5)))))))⟩

theorem inventoryIdentity085RestrictedGrowth :
    FiniteVariableRenaming.IsRestrictedGrowth
      ((⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 5]⟩⟩ : Identity Nat).lhs.toList ++
        (⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 5]⟩⟩ : Identity Nat).rhs.toList) :=
  ⟨6, FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.seen (by decide) (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.fresh (FiniteVariableRenaming.RestrictedGrowthFrom.nil 6)))))))⟩

theorem inventoryRestrictedGrowth :
    FiniteCertificate.AllRestrictedGrowth inventory := by
  rw [inventory_eq]
  exact
    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity000RestrictedGrowth <|
      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity001RestrictedGrowth <|
        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity002RestrictedGrowth <|
          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity003RestrictedGrowth <|
            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity004RestrictedGrowth <|
              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity005RestrictedGrowth <|
                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity006RestrictedGrowth <|
                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity007RestrictedGrowth <|
                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity008RestrictedGrowth <|
                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity009RestrictedGrowth <|
                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity010RestrictedGrowth <|
                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity011RestrictedGrowth <|
                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity012RestrictedGrowth <|
                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity013RestrictedGrowth <|
                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity014RestrictedGrowth <|
                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity015RestrictedGrowth <|
                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity016RestrictedGrowth <|
                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity017RestrictedGrowth <|
                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity018RestrictedGrowth <|
                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity019RestrictedGrowth <|
                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity020RestrictedGrowth <|
                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity021RestrictedGrowth <|
                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity022RestrictedGrowth <|
                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity023RestrictedGrowth <|
                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity024RestrictedGrowth <|
                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity025RestrictedGrowth <|
                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity026RestrictedGrowth <|
                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity027RestrictedGrowth <|
                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity028RestrictedGrowth <|
                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity029RestrictedGrowth <|
                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity030RestrictedGrowth <|
                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity031RestrictedGrowth <|
                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity032RestrictedGrowth <|
                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity033RestrictedGrowth <|
                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity034RestrictedGrowth <|
                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity035RestrictedGrowth <|
                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity036RestrictedGrowth <|
                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity037RestrictedGrowth <|
                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity038RestrictedGrowth <|
                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity039RestrictedGrowth <|
                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity040RestrictedGrowth <|
                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity041RestrictedGrowth <|
                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity042RestrictedGrowth <|
                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity043RestrictedGrowth <|
                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity044RestrictedGrowth <|
                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity045RestrictedGrowth <|
                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity046RestrictedGrowth <|
                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity047RestrictedGrowth <|
                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity048RestrictedGrowth <|
                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity049RestrictedGrowth <|
                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity050RestrictedGrowth <|
                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity051RestrictedGrowth <|
                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity052RestrictedGrowth <|
                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity053RestrictedGrowth <|
                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity054RestrictedGrowth <|
                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity055RestrictedGrowth <|
                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity056RestrictedGrowth <|
                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity057RestrictedGrowth <|
                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity058RestrictedGrowth <|
                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity059RestrictedGrowth <|
                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity060RestrictedGrowth <|
                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity061RestrictedGrowth <|
                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity062RestrictedGrowth <|
                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity063RestrictedGrowth <|
                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity064RestrictedGrowth <|
                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity065RestrictedGrowth <|
                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity066RestrictedGrowth <|
                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity067RestrictedGrowth <|
                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity068RestrictedGrowth <|
                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity069RestrictedGrowth <|
                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity070RestrictedGrowth <|
                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity071RestrictedGrowth <|
                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity072RestrictedGrowth <|
                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity073RestrictedGrowth <|
                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity074RestrictedGrowth <|
                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity075RestrictedGrowth <|
                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity076RestrictedGrowth <|
                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity077RestrictedGrowth <|
                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity078RestrictedGrowth <|
                                                                                                                                                                  FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity079RestrictedGrowth <|
                                                                                                                                                                    FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity080RestrictedGrowth <|
                                                                                                                                                                      FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity081RestrictedGrowth <|
                                                                                                                                                                        FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity082RestrictedGrowth <|
                                                                                                                                                                          FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity083RestrictedGrowth <|
                                                                                                                                                                            FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity084RestrictedGrowth <|
                                                                                                                                                                              FiniteNilpotentCounterexample.allRestrictedGrowth_cons inventoryIdentity085RestrictedGrowth <|
                                                                                                                                                                                FiniteNilpotentCounterexample.allRestrictedGrowth_nil

def derivationRoots :
    List SemigroupBasis.FiniteNilpotentDecisionDAG.Root :=
  [
      {
        target := ⟨⟨0, [0]⟩, ⟨0, [0, 0]⟩⟩
        basisIndex := 0
        symmetry := false
        mapping := [0]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [0, 0]⟩⟩
        basisIndex := 1
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [1, 0]⟩⟩
        basisIndex := 2
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨0, [0, 1]⟩⟩
        basisIndex := 3
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [1]⟩⟩
        basisIndex := 4
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨0, [1, 1]⟩⟩
        basisIndex := 5
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [1, 1]⟩⟩
        basisIndex := 6
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [2, 2]⟩⟩
        basisIndex := 7
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [1, 2]⟩⟩
        basisIndex := 8
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [0, 0]⟩⟩
        basisIndex := 10
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [1, 0]⟩⟩
        basisIndex := 11
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨0, [0, 1]⟩⟩
        basisIndex := 12
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨0, [1, 1]⟩⟩
        basisIndex := 13
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [1, 1]⟩⟩
        basisIndex := 14
        symmetry := false
        mapping := [0, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [2, 2]⟩⟩
        basisIndex := 15
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [1, 2]⟩⟩
        basisIndex := 16
        symmetry := false
        mapping := [0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [1, 1]⟩⟩
        basisIndex := 18
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨0, [0, 1]⟩⟩
        basisIndex := 19
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [2, 1]⟩⟩
        basisIndex := 20
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [1, 0]⟩⟩
        basisIndex := 21
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [0, 0]⟩⟩
        basisIndex := 22
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [0, 0]⟩⟩
        basisIndex := 23
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [2, 0]⟩⟩
        basisIndex := 24
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [1, 2]⟩⟩
        basisIndex := 25
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨0, [0, 2]⟩⟩
        basisIndex := 26
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨0, [2, 2]⟩⟩
        basisIndex := 27
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [3, 3]⟩⟩
        basisIndex := 28
        symmetry := false
        mapping := [1, 0, 3, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [2, 3]⟩⟩
        basisIndex := 29
        symmetry := false
        mapping := [1, 0, 3, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [2, 1]⟩⟩
        basisIndex := 31
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨1, [1, 0]⟩⟩
        basisIndex := 32
        symmetry := false
        mapping := [1, 0]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [2, 0]⟩⟩
        basisIndex := 33
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨0, [0, 2]⟩⟩
        basisIndex := 34
        symmetry := false
        mapping := [1, 0, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [2, 3]⟩⟩
        basisIndex := 35
        symmetry := false
        mapping := [1, 0, 3, 2]
      },
      {
        target := ⟨⟨0, [1, 2]⟩, ⟨2, [1, 0]⟩⟩
        basisIndex := 37
        symmetry := false
        mapping := [2, 1, 0]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [2, 3, 0]⟩⟩
        basisIndex := 9
        symmetry := false
        mapping := [0, 0, 3, 2, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [2, 0, 3]⟩⟩
        basisIndex := 9
        symmetry := false
        mapping := [0, 3, 0, 2, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [0, 2, 3]⟩⟩
        basisIndex := 9
        symmetry := false
        mapping := [0, 3, 2, 0, 1]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨0, [1, 2, 3]⟩⟩
        basisIndex := 9
        symmetry := false
        mapping := [0, 3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [0]⟩, ⟨1, [2, 3, 4]⟩⟩
        basisIndex := 9
        symmetry := false
        mapping := [0, 4, 3, 2, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [2, 3, 0]⟩⟩
        basisIndex := 17
        symmetry := false
        mapping := [0, 0, 3, 2, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [2, 0, 3]⟩⟩
        basisIndex := 17
        symmetry := false
        mapping := [0, 3, 0, 2, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [0, 2, 3]⟩⟩
        basisIndex := 17
        symmetry := false
        mapping := [0, 3, 2, 0, 1]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨0, [1, 2, 3]⟩⟩
        basisIndex := 17
        symmetry := false
        mapping := [0, 3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [0, 0]⟩, ⟨1, [2, 3, 4]⟩⟩
        basisIndex := 17
        symmetry := false
        mapping := [0, 4, 3, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [3, 0, 1]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 1, 0, 3, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [0, 3, 1]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 1, 3, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨0, [2, 3, 1]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 1, 3, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 1]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 1, 4, 3, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [3, 1, 0]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 0, 1, 3, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [1, 3, 0]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 0, 3, 1, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [2, 3, 0]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 0, 3, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 0]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 0, 4, 3, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [0, 1, 3]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 3, 1, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨0, [2, 1, 3]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 3, 1, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [3, 1, 4]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 4, 1, 3, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [1, 0, 3]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 3, 0, 1, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [2, 0, 3]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 3, 0, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [3, 0, 4]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 4, 0, 3, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨0, [1, 2, 3]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [1, 3, 4]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 4, 3, 1, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [0, 2, 3]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 3, 2, 0, 1]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [0, 3, 4]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 4, 3, 0, 2]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨1, [2, 3, 4]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 4, 3, 2, 1]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨0, [2, 3, 4]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 4, 3, 2, 0]
      },
      {
        target := ⟨⟨0, [1, 1]⟩, ⟨2, [3, 4, 5]⟩⟩
        basisIndex := 30
        symmetry := false
        mapping := [1, 0, 5, 4, 3, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [3, 0, 1]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 1, 0, 3, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [0, 3, 1]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 1, 3, 0, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨0, [2, 3, 1]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 1, 3, 2, 0]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 1]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 1, 4, 3, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [3, 1, 0]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 0, 1, 3, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [1, 3, 0]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 0, 3, 1, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨1, [2, 3, 0]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 0, 3, 2, 1]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 0]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 0, 4, 3, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [0, 1, 3]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 3, 1, 0, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨0, [2, 1, 3]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 3, 1, 2, 0]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [3, 1, 4]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 4, 1, 3, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [1, 0, 3]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 3, 0, 1, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨1, [2, 0, 3]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 3, 0, 2, 1]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [3, 0, 4]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 4, 0, 3, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨0, [1, 2, 3]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 3, 2, 1, 0]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [1, 3, 4]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 4, 3, 1, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨1, [0, 2, 3]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 3, 2, 0, 1]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [0, 3, 4]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 4, 3, 0, 2]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨1, [2, 3, 4]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 4, 3, 2, 1]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨0, [2, 3, 4]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 4, 3, 2, 0]
      },
      {
        target := ⟨⟨0, [0, 1]⟩, ⟨2, [3, 4, 5]⟩⟩
        basisIndex := 36
        symmetry := false
        mapping := [1, 0, 5, 4, 3, 2]
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

def certificate : SemigroupBasis.Generated.Order6Nilpotent.Signature0f62c5e540ab.SignatureCertificate where
  toCommon := toCommon
  listed := listed

end SemigroupBasis.Generated.Order6Nilpotent.Certificates.Cutoff4.Signature0f62c5e540ab

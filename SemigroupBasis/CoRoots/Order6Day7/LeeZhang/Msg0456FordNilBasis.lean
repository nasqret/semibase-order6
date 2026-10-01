import SemigroupBasis.ChainReplay
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0446NilZ2Presentation
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0456GuardedSwapCore
import SemigroupBasis.Examples.LeftRegularBandThree

/-! Exact msg0456 B23, literal subdirect maps, and guarded swap transport.
No unrestricted completeness field is asserted in this foundation module. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

open SemigroupBasis

def swap00 : Identity Nat := ⟨⟨0, [1, 2, 3, 0, 2]⟩, ⟨0, [1, 2, 3, 2, 0]⟩⟩
def swap01 : Identity Nat := ⟨⟨0, [1, 0, 2, 3, 2]⟩, ⟨0, [1, 2, 0, 3, 2]⟩⟩
def swap02 : Identity Nat := ⟨⟨2, [1, 0, 2, 3, 0]⟩, ⟨2, [1, 2, 0, 3, 0]⟩⟩
def swaps : List (Identity Nat) := [swap00, swap01, swap02]
def basis : List (Identity Nat) := Msg0446NilZ2.Ford.basis ++ swaps
def basisSHA256 : String := "dd1c24443052c7e34899c23fbe6b8114038e46d2b525be2fc255676d2dd8c6c4"

abbrev table6543 := Msg0446NilZ2.Ford.table6543
abbrev table6605 := Msg0446NilZ2.Ford.table6605
abbrev fordTable := Examples.leftRegularBandThree
abbrev m18Table := Generated.Catalogue.S5_254.table

theorem basis_length : basis.length = 23 := rfl

theorem old_basis_subset : ∀ identity, identity ∈ Msg0446NilZ2.Ford.basis → identity ∈ basis := by
  intro identity member
  exact List.mem_append_left swaps member

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

theorem swaps_models6543 : Models table6543.semigroup swaps :=
  FiniteCertificate.checkModels_sound table6543 swaps toFinFour (by decide +kernel)

theorem swaps_models6605 : Models table6605.semigroup swaps :=
  FiniteCertificate.checkModels_sound table6605 swaps toFinFour (by decide +kernel)

theorem models6543 : Models table6543.semigroup basis := by
  intro identity member
  rcases List.mem_append.mp member with old | added
  · exact Msg0446NilZ2.Ford.models6543 identity old
  · exact swaps_models6543 identity added

theorem models6605 : Models table6605.semigroup basis := by
  intro identity member
  rcases List.mem_append.mp member with old | added
  · exact Msg0446NilZ2.Ford.models6605 identity old
  · exact swaps_models6605 identity added

theorem oppositeModels6543 : Models table6543.semigroup.opposite (reversedBasis basis) :=
  models6543.oppositeReversed

theorem oppositeModels6605 : Models table6605.semigroup.opposite (reversedBasis basis) :=
  models6605.oppositeReversed

def fordMap (value : Fin 6) : Fin 3 :=
  if value = 3 ∨ value = 4 then 1 else if value = 5 then 2 else 0

def fordSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 3 else 5

def m18Map (value : Fin 6) : Fin 5 :=
  if value = 0 ∨ value = 5 then 0 else if value = 1 then 1
  else if value = 2 then 2 else if value = 3 then 3 else 4

def m18Section (value : Fin 5) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 1
  else if value = 2 then 2 else if value = 3 then 3 else 4

def fordProjection6543 : SplitSurjection table6543.semigroup fordTable.semigroup where
  toFun := fordMap
  map_mul := by decide
  preimage := fordSection
  right_inverse := by decide

def fordProjection6605 : SplitSurjection table6605.semigroup fordTable.semigroup where
  toFun := fordMap
  map_mul := by decide
  preimage := fordSection
  right_inverse := by decide

def m18Projection6543 : SplitSurjection table6543.semigroup m18Table.semigroup where
  toFun := m18Map
  map_mul := by decide
  preimage := m18Section
  right_inverse := by decide

def m18Projection6605 : SplitSurjection table6605.semigroup m18Table.semigroup.opposite where
  toFun := m18Map
  map_mul := by decide
  preimage := m18Section
  right_inverse := by decide

def subdirect6543 : SubdirectPair table6543.semigroup fordTable.semigroup m18Table.semigroup where
  left := fordProjection6543
  right := m18Projection6543
  jointlyInjective := by unfold Function.Injective; decide

def subdirect6605 : SubdirectPair table6605.semigroup fordTable.semigroup m18Table.semigroup.opposite where
  left := fordProjection6605
  right := m18Projection6605
  jointlyInjective := by unfold Function.Injective; decide

theorem valid6543_iff_factors {α : Type} (identity : Identity α) :
    identity.SatisfiedBy table6543.semigroup ↔
      identity.SatisfiedBy fordTable.semigroup ∧ identity.SatisfiedBy m18Table.semigroup :=
  subdirect6543.satisfiedBy_iff identity

theorem valid6605_iff_factors {α : Type} (identity : Identity α) :
    identity.SatisfiedBy table6605.semigroup ↔
      identity.SatisfiedBy fordTable.semigroup ∧ identity.SatisfiedBy m18Table.semigroup.opposite :=
  subdirect6605.satisfiedBy_iff identity

theorem fordModels : Models fordTable.semigroup basis := by
  intro identity member
  exact fordProjection6543.pushforwardIdentity identity (models6543 identity member)

theorem m18Models : Models m18Table.semigroup basis := by
  intro identity member
  exact m18Projection6543.pushforwardIdentity identity (models6543 identity member)

theorem m18OppositeModels : Models m18Table.semigroup.opposite basis := by
  intro identity member
  exact m18Projection6605.pushforwardIdentity identity (models6605 identity member)

private def chainZwzPrefix : ChainReplay.Chain Nat :=
  [⟨12, .forward, [], [], [[0], [2], [3]]⟩]

theorem balancedZwzPrefix :
    Derives basis SemigroupBasis.CoRoots.S5_254.zwzPrefixLaw.lhs SemigroupBasis.CoRoots.S5_254.zwzPrefixLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainZwzPrefix) (by decide)

private def chainDoubleZPrefix : ChainReplay.Chain Nat :=
  [⟨4, .forward, [], [], [[0], [2]]⟩]

theorem balancedDoubleZPrefix :
    Derives basis SemigroupBasis.CoRoots.S5_254.doubleZPrefixLaw.lhs SemigroupBasis.CoRoots.S5_254.doubleZPrefixLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainDoubleZPrefix) (by decide)

private def chainLongZwzTransport : ChainReplay.Chain Nat :=
  [⟨21, .forward, [], [], [[0], [1], [2], [3]]⟩]

theorem balancedLongZwzTransport :
    Derives basis SemigroupBasis.CoRoots.S5_254.longZwzTransportLaw.lhs SemigroupBasis.CoRoots.S5_254.longZwzTransportLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainLongZwzTransport) (by decide)

private def chainDoubleZTransport : ChainReplay.Chain Nat :=
  [⟨13, .forward, [], [], [[0], [1], [2], [3]]⟩]

theorem balancedDoubleZTransport :
    Derives basis SemigroupBasis.CoRoots.S5_254.doubleZTransportLaw.lhs SemigroupBasis.CoRoots.S5_254.doubleZTransportLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainDoubleZTransport) (by decide)

private def chainCrossedWZ : ChainReplay.Chain Nat :=
  [⟨20, .forward, [], [], [[0], [1], [2], [3]]⟩]

theorem balancedCrossedWZ :
    Derives basis SemigroupBasis.CoRoots.S5_254.crossedWZLaw.lhs SemigroupBasis.CoRoots.S5_254.crossedWZLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainCrossedWZ) (by decide)

private def chainWzCrossing : ChainReplay.Chain Nat :=
  [⟨17, .forward, [], [], [[0], [2], [3]]⟩]

theorem balancedWzCrossing :
    Derives basis SemigroupBasis.CoRoots.S5_254.wzCrossingLaw.lhs SemigroupBasis.CoRoots.S5_254.wzCrossingLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainWzCrossing) (by decide)

private def chainTerminalZTransport : ChainReplay.Chain Nat :=
  [⟨13, .backward, [], [], [[0], [1], [2], [3]]⟩,
   ⟨14, .forward, [], [], [[0], [1], [2], [3]]⟩]

theorem balancedTerminalZTransport :
    Derives basis SemigroupBasis.CoRoots.S5_254.terminalZTransportLaw.lhs SemigroupBasis.CoRoots.S5_254.terminalZTransportLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainTerminalZTransport) (by decide)

private def chainAlternatingZ : ChainReplay.Chain Nat :=
  [⟨4, .backward, [], [], [[0], [2]]⟩,
   ⟨19, .forward, [], [], [[0], [2]]⟩]

theorem balancedAlternatingZ :
    Derives basis SemigroupBasis.CoRoots.S5_254.alternatingZLaw.lhs SemigroupBasis.CoRoots.S5_254.alternatingZLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainAlternatingZ) (by decide)

theorem guardedCoreBasisDerivable : ∀ identity, identity ∈ FordSwapCore.basis →
    Derives basis identity.lhs identity.rhs := by
  intro identity member
  simp only [FordSwapCore.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact balancedZwzPrefix
  · exact balancedDoubleZPrefix
  · exact balancedLongZwzTransport
  · exact balancedDoubleZTransport
  · exact balancedCrossedWZ
  · exact balancedWzCrossing
  · exact balancedTerminalZTransport
  · exact balancedAlternatingZ

theorem transportGuardedList {left right : List Nat}
    (derivation : S5_107.ListDerives FordSwapCore.basis left right) :
    S5_107.ListDerives basis left right := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | words wordDerivation =>
      exact S5_107.ListDerives.words (wordDerivation.transport guardedCoreBasisDerivable)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordNil

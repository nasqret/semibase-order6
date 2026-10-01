import SemigroupBasis.ChainReplay
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463BalancedCore
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0455SeparatedCubeSemantics

/-! Exact msg0463 B12 and the count-preserving M18 rule interface.
The stronger M18 power and sandwich-contraction laws are NOT transported.
Each of the thirteen balanced bridges is an explicit checked finite chain;
its subsequent word substitution is unrestricted and nonempty. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2

open SemigroupBasis

def basis : List (Identity Nat) :=
  Msg0455NilZ2.basis ++ [Msg0455NilZ2.separatedCube]
def basisSHA256 : String := "98c9cab9ee956f0041374e491454cbb0871942d953bea1b0655b4fe4a38bfdb4"
abbrev target := Msg0446NilZ2.table9386

theorem basis_length : basis.length = 12 := rfl

theorem old_basis_subset : ∀ identity, identity ∈ Msg0455NilZ2.basis → identity ∈ basis := by
  intro identity member
  exact List.mem_append_left _ member

theorem models9386 : Models target.semigroup basis := by
  intro identity member
  rcases List.mem_append.mp member with old | added
  · exact Msg0455NilZ2.models9386 identity old
  · simp only [List.mem_singleton] at added
    subst identity
    exact Msg0455NilZ2.separatedCube_valid9386

theorem oppositeModels9386 : Models target.semigroup.opposite (reversedBasis basis) :=
  models9386.oppositeReversed

theorem derives_preserve_signature {left right : Word Nat}
    (derivation : Derives basis left right) : Msg0446NilZ2.SameSignature left right :=
  Msg0446NilZ2.sameSignature_of_valid9386 ⟨left, right⟩ (derivation.sound models9386)

private def chainPrefixRotation : ChainReplay.Chain Nat :=
  [⟨1, .forward, [], [], [[0], [1]]⟩]

theorem balancedPrefixRotation :
    Derives basis S5_254.prefixRotationLaw.lhs S5_254.prefixRotationLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainPrefixRotation) (by decide)

theorem derivesPrefixRotationSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.prefixRotationLaw.lhs.bind substitution) (S5_254.prefixRotationLaw.rhs.bind substitution) :=
  Derives.subst balancedPrefixRotation substitution

private def chainZwzPrefix : ChainReplay.Chain Nat :=
  [⟨3, .forward, [], [], [[0], [2], [3]]⟩]

theorem balancedZwzPrefix :
    Derives basis S5_254.zwzPrefixLaw.lhs S5_254.zwzPrefixLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainZwzPrefix) (by decide)

theorem derivesZwzPrefixSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.zwzPrefixLaw.lhs.bind substitution) (S5_254.zwzPrefixLaw.rhs.bind substitution) :=
  Derives.subst balancedZwzPrefix substitution

private def chainDoubleZPrefix : ChainReplay.Chain Nat :=
  [⟨2, .forward, [], [], [[0], [2]]⟩]

theorem balancedDoubleZPrefix :
    Derives basis S5_254.doubleZPrefixLaw.lhs S5_254.doubleZPrefixLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainDoubleZPrefix) (by decide)

theorem derivesDoubleZPrefixSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.doubleZPrefixLaw.lhs.bind substitution) (S5_254.doubleZPrefixLaw.rhs.bind substitution) :=
  Derives.subst balancedDoubleZPrefix substitution

private def chainWyRotation : ChainReplay.Chain Nat :=
  [⟨3, .backward, [], [], [[0], [1], [3]]⟩,
   ⟨1, .forward, [], [3, 1], [[0], [1]]⟩]

theorem balancedWyRotation :
    Derives basis S5_254.wyRotationLaw.lhs S5_254.wyRotationLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainWyRotation) (by decide)

theorem derivesWyRotationSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.wyRotationLaw.lhs.bind substitution) (S5_254.wyRotationLaw.rhs.bind substitution) :=
  Derives.subst balancedWyRotation substitution

private def chainAlternatingPair : ChainReplay.Chain Nat :=
  [⟨2, .backward, [], [], [[0], [1]]⟩,
   ⟨1, .forward, [], [1], [[0], [1]]⟩]

theorem balancedAlternatingPair :
    Derives basis S5_254.alternatingPairLaw.lhs S5_254.alternatingPairLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainAlternatingPair) (by decide)

theorem derivesAlternatingPairSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.alternatingPairLaw.lhs.bind substitution) (S5_254.alternatingPairLaw.rhs.bind substitution) :=
  Derives.subst balancedAlternatingPair substitution

private def chainLongZwzTransport : ChainReplay.Chain Nat :=
  [⟨8, .forward, [], [], [[0], [1], [2], [3]]⟩]

theorem balancedLongZwzTransport :
    Derives basis S5_254.longZwzTransportLaw.lhs S5_254.longZwzTransportLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainLongZwzTransport) (by decide)

theorem derivesLongZwzTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.longZwzTransportLaw.lhs.bind substitution) (S5_254.longZwzTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedLongZwzTransport substitution

private def chainDoubleZTransport : ChainReplay.Chain Nat :=
  [⟨1, .backward, [], [], [[2], [0, 1, 0]]⟩,
   ⟨4, .forward, [], [], [[2], [0], [1]]⟩]

theorem balancedDoubleZTransport :
    Derives basis S5_254.doubleZTransportLaw.lhs S5_254.doubleZTransportLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainDoubleZTransport) (by decide)

theorem derivesDoubleZTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.doubleZTransportLaw.lhs.bind substitution) (S5_254.doubleZTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedDoubleZTransport substitution

private def chainCrossedWZ : ChainReplay.Chain Nat :=
  [⟨7, .forward, [], [], [[0], [1], [2], [3]]⟩]

theorem balancedCrossedWZ :
    Derives basis S5_254.crossedWZLaw.lhs S5_254.crossedWZLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainCrossedWZ) (by decide)

theorem derivesCrossedWZSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.crossedWZLaw.lhs.bind substitution) (S5_254.crossedWZLaw.rhs.bind substitution) :=
  Derives.subst balancedCrossedWZ substitution

private def chainWyPrefixTransport : ChainReplay.Chain Nat :=
  [⟨10, .forward, [], [], [[0], [2], [1], [3]]⟩]

theorem balancedWyPrefixTransport :
    Derives basis S5_254.wyPrefixTransportLaw.lhs S5_254.wyPrefixTransportLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainWyPrefixTransport) (by decide)

theorem derivesWyPrefixTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.wyPrefixTransportLaw.lhs.bind substitution) (S5_254.wyPrefixTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedWyPrefixTransport substitution

private def chainTerminalYTransport : ChainReplay.Chain Nat :=
  [⟨6, .forward, [], [], [[0], [1], [2], [3]]⟩]

theorem balancedTerminalYTransport :
    Derives basis S5_254.terminalYTransportLaw.lhs S5_254.terminalYTransportLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainTerminalYTransport) (by decide)

theorem derivesTerminalYTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.terminalYTransportLaw.lhs.bind substitution) (S5_254.terminalYTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedTerminalYTransport substitution

private def chainTerminalZTransport : ChainReplay.Chain Nat :=
  [⟨4, .backward, [], [], [[2], [0], [1]]⟩,
   ⟨1, .forward, [], [0], [[2], [0, 1]]⟩]

theorem balancedTerminalZTransport :
    Derives basis S5_254.terminalZTransportLaw.lhs S5_254.terminalZTransportLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainTerminalZTransport) (by decide)

theorem derivesTerminalZTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.terminalZTransportLaw.lhs.bind substitution) (S5_254.terminalZTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedTerminalZTransport substitution

private def chainWzCrossing : ChainReplay.Chain Nat :=
  [⟨5, .forward, [], [], [[0], [2], [3]]⟩]

theorem balancedWzCrossing :
    Derives basis S5_254.wzCrossingLaw.lhs S5_254.wzCrossingLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainWzCrossing) (by decide)

theorem derivesWzCrossingSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.wzCrossingLaw.lhs.bind substitution) (S5_254.wzCrossingLaw.rhs.bind substitution) :=
  Derives.subst balancedWzCrossing substitution

private def chainAlternatingZ : ChainReplay.Chain Nat :=
  [⟨2, .backward, [], [], [[0], [2]]⟩,
   ⟨1, .backward, [0], [], [[2], [0]]⟩]

theorem balancedAlternatingZ :
    Derives basis S5_254.alternatingZLaw.lhs S5_254.alternatingZLaw.rhs :=
  ChainReplay.check_sound (denseIndex := ChainReplay.natDenseIndex)
    (chain := chainAlternatingZ) (by decide)

theorem derivesAlternatingZSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.alternatingZLaw.lhs.bind substitution) (S5_254.alternatingZLaw.rhs.bind substitution) :=
  Derives.subst balancedAlternatingZ substitution

/-- Every rule of the independent balanced core has an actual B12 derivation. -/
theorem balancedBasisDerivable : ∀ identity, identity ∈ BalancedCore.basis →
    Derives basis identity.lhs identity.rhs := by
  intro identity member
  simp only [BalancedCore.basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact balancedPrefixRotation
  · exact balancedZwzPrefix
  · exact balancedDoubleZPrefix
  · exact balancedWyRotation
  · exact balancedAlternatingPair
  · exact balancedLongZwzTransport
  · exact balancedDoubleZTransport
  · exact balancedCrossedWZ
  · exact balancedWyPrefixTransport
  · exact balancedTerminalYTransport
  · exact balancedTerminalZTransport
  · exact balancedWzCrossing
  · exact balancedAlternatingZ

theorem transportBalancedList {left right : List Nat}
    (derivation : S5_107.ListDerives BalancedCore.basis left right) :
    S5_107.ListDerives basis left right := by
  cases derivation with
  | empty => exact S5_107.ListDerives.empty
  | words wordDerivation => exact S5_107.ListDerives.words (wordDerivation.transport balancedBasisDerivable)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463NilZ2

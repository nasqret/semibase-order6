import SemigroupBasis.CoRoots.S5_254
import SemigroupBasis.CoRoots.S5_107ListDerives

/-! The thirteen count-preserving M18 laws as an independent algebraic core.
Neither the M18 square power law nor sandwich contraction is included.
This module asserts no table completeness. A later target must derive every
one of these thirteen laws before transporting the unbounded core proof. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.BalancedCore

open SemigroupBasis

def basis : List (Identity Nat) :=
  [S5_254.prefixRotationLaw,
   S5_254.zwzPrefixLaw,
   S5_254.doubleZPrefixLaw,
   S5_254.wyRotationLaw,
   S5_254.alternatingPairLaw,
   S5_254.longZwzTransportLaw,
   S5_254.doubleZTransportLaw,
   S5_254.crossedWZLaw,
   S5_254.wyPrefixTransportLaw,
   S5_254.terminalYTransportLaw,
   S5_254.terminalZTransportLaw,
   S5_254.wzCrossingLaw,
   S5_254.alternatingZLaw]

theorem basis_length : basis.length = 13 := rfl
theorem basis_eq_M18_drop_two : basis = S5_254.basis.drop 2 := rfl

theorem balancedPrefixRotation : Derives basis S5_254.prefixRotationLaw.lhs S5_254.prefixRotationLaw.rhs :=
  Derives.fromBasis (e := S5_254.prefixRotationLaw) (by decide)

theorem derivesPrefixRotationSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.prefixRotationLaw.lhs.bind substitution) (S5_254.prefixRotationLaw.rhs.bind substitution) :=
  Derives.subst balancedPrefixRotation substitution

theorem balancedZwzPrefix : Derives basis S5_254.zwzPrefixLaw.lhs S5_254.zwzPrefixLaw.rhs :=
  Derives.fromBasis (e := S5_254.zwzPrefixLaw) (by decide)

theorem derivesZwzPrefixSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.zwzPrefixLaw.lhs.bind substitution) (S5_254.zwzPrefixLaw.rhs.bind substitution) :=
  Derives.subst balancedZwzPrefix substitution

theorem balancedDoubleZPrefix : Derives basis S5_254.doubleZPrefixLaw.lhs S5_254.doubleZPrefixLaw.rhs :=
  Derives.fromBasis (e := S5_254.doubleZPrefixLaw) (by decide)

theorem derivesDoubleZPrefixSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.doubleZPrefixLaw.lhs.bind substitution) (S5_254.doubleZPrefixLaw.rhs.bind substitution) :=
  Derives.subst balancedDoubleZPrefix substitution

theorem balancedWyRotation : Derives basis S5_254.wyRotationLaw.lhs S5_254.wyRotationLaw.rhs :=
  Derives.fromBasis (e := S5_254.wyRotationLaw) (by decide)

theorem derivesWyRotationSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.wyRotationLaw.lhs.bind substitution) (S5_254.wyRotationLaw.rhs.bind substitution) :=
  Derives.subst balancedWyRotation substitution

theorem balancedAlternatingPair : Derives basis S5_254.alternatingPairLaw.lhs S5_254.alternatingPairLaw.rhs :=
  Derives.fromBasis (e := S5_254.alternatingPairLaw) (by decide)

theorem derivesAlternatingPairSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.alternatingPairLaw.lhs.bind substitution) (S5_254.alternatingPairLaw.rhs.bind substitution) :=
  Derives.subst balancedAlternatingPair substitution

theorem balancedLongZwzTransport : Derives basis S5_254.longZwzTransportLaw.lhs S5_254.longZwzTransportLaw.rhs :=
  Derives.fromBasis (e := S5_254.longZwzTransportLaw) (by decide)

theorem derivesLongZwzTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.longZwzTransportLaw.lhs.bind substitution) (S5_254.longZwzTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedLongZwzTransport substitution

theorem balancedDoubleZTransport : Derives basis S5_254.doubleZTransportLaw.lhs S5_254.doubleZTransportLaw.rhs :=
  Derives.fromBasis (e := S5_254.doubleZTransportLaw) (by decide)

theorem derivesDoubleZTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.doubleZTransportLaw.lhs.bind substitution) (S5_254.doubleZTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedDoubleZTransport substitution

theorem balancedCrossedWZ : Derives basis S5_254.crossedWZLaw.lhs S5_254.crossedWZLaw.rhs :=
  Derives.fromBasis (e := S5_254.crossedWZLaw) (by decide)

theorem derivesCrossedWZSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.crossedWZLaw.lhs.bind substitution) (S5_254.crossedWZLaw.rhs.bind substitution) :=
  Derives.subst balancedCrossedWZ substitution

theorem balancedWyPrefixTransport : Derives basis S5_254.wyPrefixTransportLaw.lhs S5_254.wyPrefixTransportLaw.rhs :=
  Derives.fromBasis (e := S5_254.wyPrefixTransportLaw) (by decide)

theorem derivesWyPrefixTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.wyPrefixTransportLaw.lhs.bind substitution) (S5_254.wyPrefixTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedWyPrefixTransport substitution

theorem balancedTerminalYTransport : Derives basis S5_254.terminalYTransportLaw.lhs S5_254.terminalYTransportLaw.rhs :=
  Derives.fromBasis (e := S5_254.terminalYTransportLaw) (by decide)

theorem derivesTerminalYTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.terminalYTransportLaw.lhs.bind substitution) (S5_254.terminalYTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedTerminalYTransport substitution

theorem balancedTerminalZTransport : Derives basis S5_254.terminalZTransportLaw.lhs S5_254.terminalZTransportLaw.rhs :=
  Derives.fromBasis (e := S5_254.terminalZTransportLaw) (by decide)

theorem derivesTerminalZTransportSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.terminalZTransportLaw.lhs.bind substitution) (S5_254.terminalZTransportLaw.rhs.bind substitution) :=
  Derives.subst balancedTerminalZTransport substitution

theorem balancedWzCrossing : Derives basis S5_254.wzCrossingLaw.lhs S5_254.wzCrossingLaw.rhs :=
  Derives.fromBasis (e := S5_254.wzCrossingLaw) (by decide)

theorem derivesWzCrossingSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.wzCrossingLaw.lhs.bind substitution) (S5_254.wzCrossingLaw.rhs.bind substitution) :=
  Derives.subst balancedWzCrossing substitution

theorem balancedAlternatingZ : Derives basis S5_254.alternatingZLaw.lhs S5_254.alternatingZLaw.rhs :=
  Derives.fromBasis (e := S5_254.alternatingZLaw) (by decide)

theorem derivesAlternatingZSubstitution (substitution : Nat → Word Nat) :
    Derives basis (S5_254.alternatingZLaw.lhs.bind substitution) (S5_254.alternatingZLaw.rhs.bind substitution) :=
  Derives.subst balancedAlternatingZ substitution

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.BalancedCore

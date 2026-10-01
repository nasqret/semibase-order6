import SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802OppositeNormal
import SemigroupBasis.CoRoots.Order6FordLordAe8Normal
import SemigroupBasis.CoRoots.S5_794Family
import SemigroupBasis.FiniteNilpotent
import SemigroupBasis.Generated.S3_15

set_option maxRecDepth 100000

/-!
# Dual transfer for the corrected ae8 Ford--Lord system

The eight displayed ae8 laws are the word-reversal dual of the committed
`Sigma_0b1bf8949e267cbb` system, up to a permutation of the laws, independent
variable renamings, and equality symmetry in exactly two cases.  This module
records both directions of that finite syntactic transport, dualizes the
existing `S3_13 x S5_802.opposite` intersection theorem, and transfers the
two factor theories to the three ae8 factor pairs.
-/

namespace SemigroupBasis.CoRoots.Order6FordLordAe8DualTransfer

open SemigroupBasis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_0b1bf8949e267cbb.basis

private abbrev dualBasis : List (Identity Nat) :=
  reversedBasis sourceBasis

private abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FordLordAe8.basis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

/-! The source laws in displayed order. -/

private def b1 : Identity Nat :=
  Identity.mk (w 0 [0]) (w 0 [0, 0])

private def b2 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])

private def b3 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])

private def b4 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1])

private def b5 : Identity Nat :=
  Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])

private def b6 : Identity Nat :=
  Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0])

private def b7 : Identity Nat :=
  Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2])

private def b8 : Identity Nat :=
  Identity.mk (w 0 [1, 1, 2, 2]) (w 0 [2, 1, 1, 2])

private theorem sourceBasis_eq :
    sourceBasis = [b1, b2, b3, b4, b5, b6, b7, b8] := by
  decide

/-! The target laws in displayed order. -/

private def a1 : Identity Nat :=
  Identity.mk (w 0 [0]) (w 0 [0, 0])

private def a2 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0])

private def a3 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])

private def a4 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 1, 2]) (w 0 [1, 1, 0, 2])

private def a5 : Identity Nat :=
  Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1])

private def a6 : Identity Nat :=
  Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0])

private def a7 : Identity Nat :=
  Identity.mk (w 0 [1, 0, 2, 0]) (w 0 [1, 2, 0])

private def a8 : Identity Nat :=
  Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2])

private theorem targetBasis_eq :
    targetBasis = [a1, a2, a3, a4, a5, a6, a7, a8] := by
  decide

private def swap01 : Nat -> Nat
  | 0 => 1
  | 1 => 0
  | n => n

private def swap12 : Nat -> Nat
  | 1 => 2
  | 2 => 1
  | n => n

private def swap02 : Nat -> Nat
  | 0 => 2
  | 2 => 0
  | n => n

/-- `0 -> 1`, `1 -> 2`, `2 -> 0`. -/
private def cycleForward : Nat -> Nat
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | n => n

/-- `0 -> 2`, `1 -> 0`, `2 -> 1`. -/
private def cycleBackward : Nat -> Nat
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | n => n

private theorem derivesReversedSource (identity : Identity Nat)
    (member : identity ∈ sourceBasis) :
    Derives dualBasis identity.lhs.reverse identity.rhs.reverse := by
  exact Derives.fromBasis
    (List.mem_map.mpr ⟨identity, member, rfl⟩)

/-- Every reversed source axiom is derivable from the corrected ae8 basis. -/
private theorem dualAxiomsDeriveTarget :
    forall identity : Identity Nat, identity ∈ dualBasis ->
      Derives targetBasis identity.lhs identity.rhs := by
  intro identity member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  rw [sourceBasis_eq] at sourceMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at sourceMember
  rcases sourceMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [b1, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLordAe8.derivesPower
        (Word.singleton 0))
  · simpa [b2, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLordAe8.derivesRightDuplication
        (Word.singleton 0) (Word.singleton 1)).symm
  · simpa [b3, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLordAe8.derivesSquareInterleave
        (Word.singleton 1) (Word.singleton 0))
  · simpa [b4, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLordAe8.derivesTailTransport
        (Word.singleton 1) (Word.singleton 2) (Word.singleton 0))
  · simpa [b5, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLordAe8.derivesLeftCollapse
        (Word.singleton 0) (Word.singleton 1)).symm
  · simpa [b6, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLordAe8.derivesMiddleCollapse
        (Word.singleton 0) (Word.singleton 2) (Word.singleton 1))
  · simpa [b7, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLordAe8.derivesLeftTransport
        (Word.singleton 2) (Word.singleton 0) (Word.singleton 1))
  · simpa [b8, w, Identity.reversed, Word.reverse, Word.reverseAux,
      Word.singleton, Word.append] using
      (SemigroupBasis.CoRoots.Order6FordLordAe8.derivesPlasmaLordForget
        (Word.singleton 2) (Word.singleton 1) (Word.singleton 0))

/-- Every corrected ae8 axiom is derivable from the reversed source basis. -/
private theorem targetAxiomsDeriveDual :
    forall identity : Identity Nat, identity ∈ targetBasis ->
      Derives dualBasis identity.lhs identity.rhs := by
  intro identity member
  rw [targetBasis_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [a1, b1, w, Word.reverse, Word.reverseAux] using
      (derivesReversedSource b1 (by decide))
  · simpa [a2, b5, w, Word.reverse, Word.reverseAux] using
      (derivesReversedSource b5 (by decide)).symm
  · simpa [a3, b3, w, Word.reverse, Word.reverseAux, Word.map, swap01] using
      (derivesReversedSource b3 (by decide)).rename swap01
  · simpa [a4, b8, w, Word.reverse, Word.reverseAux, Word.map, swap02] using
      (derivesReversedSource b8 (by decide)).rename swap02
  · simpa [a5, b7, w, Word.reverse, Word.reverseAux, Word.map,
      cycleForward] using
      (derivesReversedSource b7 (by decide)).rename cycleForward
  · simpa [a6, b2, w, Word.reverse, Word.reverseAux] using
      (derivesReversedSource b2 (by decide)).symm
  · simpa [a7, b6, w, Word.reverse, Word.reverseAux, Word.map, swap12] using
      (derivesReversedSource b6 (by decide)).rename swap12
  · simpa [a8, b4, w, Word.reverse, Word.reverseAux, Word.map,
      cycleBackward] using
      (derivesReversedSource b4 (by decide)).rename cycleBackward

private theorem sameTheoryOfCommonBasis
    {G : Semigroup S} {H : Semigroup T}
    {common : List (Identity Nat)}
    (basisForG : BasisFor G common) (basisForH : BasisFor H common)
    (identity : Identity Nat) :
    identity.SatisfiedBy G ↔ identity.SatisfiedBy H := by
  constructor
  · intro valid valuation
    exact (basisForG.2 identity valid).sound basisForH.1 valuation
  · intro valid valuation
    exact (basisForH.2 identity valid).sound basisForG.1 valuation

private def sourceDualIntersection :
    IntersectionBasis
      SemigroupBasis.Generated.S3_13.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup
      dualBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_802Opposite.intersectionBasis.oppositeLeftOfOppositeRight

private def dualIntersectionS5_794 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup
      dualBasis :=
  sourceDualIntersection.transferTheories
    (fun identity => sameTheoryOfCommonBasis
      SemigroupBasis.Generated.S3_13.opposite_basis
      SemigroupBasis.Generated.S3_15.opposite_basis identity)
    (fun identity => sameTheoryOfCommonBasis
      SemigroupBasis.CoRoots.S5_794Family.S5_802.basisFor
      SemigroupBasis.CoRoots.S5_794Family.S5_794.basisFor identity)

private def dualIntersectionS5_802 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup
      dualBasis :=
  sourceDualIntersection.transferTheories
    (fun identity => sameTheoryOfCommonBasis
      SemigroupBasis.Generated.S3_13.opposite_basis
      SemigroupBasis.Generated.S3_15.opposite_basis identity)
    (fun identity => Iff.rfl)

private def dualIntersectionS5_810 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup
      dualBasis :=
  sourceDualIntersection.transferTheories
    (fun identity => sameTheoryOfCommonBasis
      SemigroupBasis.Generated.S3_13.opposite_basis
      SemigroupBasis.Generated.S3_15.opposite_basis identity)
    (fun identity => sameTheoryOfCommonBasis
      SemigroupBasis.CoRoots.S5_794Family.S5_802.basisFor
      SemigroupBasis.CoRoots.S5_794Family.S5_810.basisFor identity)

private def replaceDualIntersection
    {G : Semigroup S} {H : Semigroup T}
    (source : IntersectionBasis G H dualBasis) :
    IntersectionBasis G H targetBasis where
  leftModels := by
    intro identity member valuation
    exact (targetAxiomsDeriveDual identity member).sound
      source.leftModels valuation
  rightModels := by
    intro identity member valuation
    exact (targetAxiomsDeriveDual identity member).sound
      source.rightModels valuation
  complete := by
    intro identity leftValid rightValid
    exact (source.complete identity leftValid rightValid).transport
      dualAxiomsDeriveTarget

def intersectionBasisS5_794 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis := by
  simpa only [targetBasis,
    SemigroupBasis.CoRoots.Order6FordLordAe8.basis_eq_displayed] using
    (replaceDualIntersection dualIntersectionS5_794)

def intersectionBasisS5_802 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis := by
  simpa only [targetBasis,
    SemigroupBasis.CoRoots.Order6FordLordAe8.basis_eq_displayed] using
    (replaceDualIntersection dualIntersectionS5_802)

def intersectionBasisS5_810 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis := by
  simpa only [targetBasis,
    SemigroupBasis.CoRoots.Order6FordLordAe8.basis_eq_displayed] using
    (replaceDualIntersection dualIntersectionS5_810)

end SemigroupBasis.CoRoots.Order6FordLordAe8DualTransfer

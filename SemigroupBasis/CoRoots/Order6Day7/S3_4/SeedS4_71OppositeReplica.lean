import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank096
import SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_71
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.Opposite

/-!
# Source-bound unrestricted opposite replica for `S3_4 × S4_71op`

The exact three-element factor is self-opposite under its identity map. The
exact four-element target factor is definitionally the opposite of the
already kernel-green rank-012 factor. Reversing an arbitrary identity therefore
transports both factor-validity witnesses into that independently complete
seed. All five reversed source axioms are explicitly derived from the frozen
rank-096 displayed basis. The only nonliteral law uses the association-fixed
chain `xyxx → xxyx → xxxy → xxy → xyx`.

No finite displayed-alphabet check is used as unrestricted completeness.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_71OppositeReplica

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank096.basis

private def instantiateTwo
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | marker + 2 => Word.singleton (marker + 2)

/-- The catalogue `S3_4` table equals its transpose on all nine entries. -/
def leftSelfDuality :
    Embedding Rank012.leftTable.semigroup.opposite
      Rank096.leftTable.semigroup where
  toFun := fun element => element
  map_mul := by
    intro first second
    exact by decide +revert
  injective := by
    intro first second same
    exact same

/-- Derive the sole nonliteral reversed source axiom, with typed boundaries. -/
theorem reversedAnchoredContraction :
    Derives targetBasis
      (Word.mk 0 [1, 0, 0])
      (Word.mk 0 [1, 0]) := by
  have anchor :
      Derives targetBasis
        (Word.mk 0 [0, 1])
        (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := Rank096.law02)
      (show Rank096.law02 ∈ targetBasis by decide)
  have prefixContraction :
      Derives targetBasis
        (Word.mk 0 [0, 0, 1])
        (Word.mk 0 [0, 1]) :=
    Derives.fromBasis (e := Rank096.law01)
      (show Rank096.law01 ∈ targetBasis by decide)
  have stepOne :
      Derives targetBasis
        (Word.mk 0 [1, 0, 0])
        (Word.mk 0 [0, 1, 0]) := by
    have suffixed := Derives.appendRight anchor.symm (Word.singleton 0)
    change
      Derives targetBasis
        (Word.mk 0 [1, 0, 0])
        (Word.mk 0 [0, 1, 0]) at suffixed
    exact suffixed
  have stepTwo :
      Derives targetBasis
        (Word.mk 0 [0, 1, 0])
        (Word.mk 0 [0, 0, 1]) := by
    have substituted :=
      Derives.subst anchor.symm
        (instantiateTwo (Word.singleton 0) (Word.mk 0 [1]))
    change
      Derives targetBasis
        (Word.mk 0 [0, 1, 0])
        (Word.mk 0 [0, 0, 1]) at substituted
    exact substituted
  exact stepOne.trans (stepTwo.trans (prefixContraction.trans anchor))

/-- Replay every reversed kernel-green rank-012 law into frozen rank-096. -/
theorem reversedSourceAxiomsDeriveDisplayed
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis Rank012.basis) :
    Derives targetBasis identity.lhs identity.rhs := by
  simp only [reversedBasis, Rank012.basis,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · change
      Derives targetBasis
        (Word.mk 0 [0, 0])
        (Word.mk 0 [0, 0, 0])
    exact
      Derives.fromBasis (e := Rank096.law00)
        (show Rank096.law00 ∈ targetBasis by decide)
  · change
      Derives targetBasis
        (Word.mk 1 [0, 0, 0])
        (Word.mk 1 [0, 0])
    have primitive :
        Derives targetBasis
          (Word.mk 0 [1, 1])
          (Word.mk 0 [1, 1, 1]) :=
      Derives.fromBasis (e := Rank096.law04)
        (show Rank096.law04 ∈ targetBasis by decide)
    have exchanged :=
      Derives.subst primitive.symm
        (instantiateTwo (Word.singleton 1) (Word.singleton 0))
    change
      Derives targetBasis
        (Word.mk 1 [0, 0, 0])
        (Word.mk 1 [0, 0]) at exchanged
    exact exchanged
  · exact reversedAnchoredContraction
  · change
      Derives targetBasis
        (Word.mk 1 [1, 0, 0])
        (Word.mk 0 [1, 1, 0])
    have primitive :
        Derives targetBasis
          (Word.mk 0 [0, 1, 1])
          (Word.mk 1 [0, 0, 1]) :=
      Derives.fromBasis (e := Rank096.law03)
        (show Rank096.law03 ∈ targetBasis by decide)
    have exchanged :=
      Derives.subst primitive
        (instantiateTwo (Word.singleton 1) (Word.singleton 0))
    change
      Derives targetBasis
        (Word.mk 1 [1, 0, 0])
        (Word.mk 0 [1, 1, 0]) at exchanged
    exact exchanged
  · change
      Derives targetBasis
        (Word.mk 0 [1, 0])
        (Word.mk 0 [0, 1])
    exact
      (Derives.fromBasis (e := Rank096.law02)
        (show Rank096.law02 ∈ targetBasis by decide)).symm

/-- Reverse exact factor validity, apply the source seed, replay its laws. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank096.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank096.rightTable.semigroup) :
    Derives targetBasis identity.lhs identity.rhs := by
  have sourceLeft :
      identity.reversed.SatisfiedBy Rank012.leftTable.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed identity
      Rank012.leftTable.semigroup).mp
      (leftSelfDuality.pullback_identity identity leftValid)
  have sourceRight :
      identity.reversed.SatisfiedBy Rank012.rightTable.semigroup := by
    have oppositeValid :
        identity.SatisfiedBy Rank012.rightTable.semigroup.opposite := by
      change identity.SatisfiedBy Rank096.rightTable.semigroup
      exact rightValid
    exact
      (Identity.satisfiedBy_opposite_iff_reversed identity
        Rank012.rightTable.semigroup).mp oppositeValid
  have source :=
    SeedS4_71.derivesOfFactorValid identity.reversed sourceLeft sourceRight
  have returned :
      Derives (reversedBasis Rank012.basis) identity.lhs identity.rhs := by
    simpa [Identity.reversed] using source.reverse
  exact returned.transport reversedSourceAxiomsDeriveDisplayed

/-- Unrestricted completeness precedes every quotient-normalizer operation. -/
def intersectionBasis :
    IntersectionBasis
      Rank096.leftTable.semigroup
      Rank096.rightTable.semigroup
      Rank096.basis where
  leftModels := Rank096.leftModels
  rightModels := Rank096.rightModels
  complete := derivesOfFactorValid

noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank096.leftTable.semigroup
      Rank096.rightTable.semigroup
      Rank096.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem representative_basis_S6_9618 :
    BasisFor Rank096.S6_9618.table.semigroup Rank096.basis :=
  Rank096.S6_9618.representative_basis_of_normalizer intersectionNormalizer

theorem opposite_basis_S6_9618 :
    BasisFor Rank096.S6_9618.table.semigroup.opposite
      (reversedBasis Rank096.basis) :=
  Rank096.S6_9618.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_4.SeedS4_71OppositeReplica

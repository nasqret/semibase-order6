import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank016
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_303Completeness

/-!
# An unrestricted `S2_4 × S5_303` family seed

The rank-016 shell authenticates the finite displayed laws and the exact
split-subdirect maps, but deliberately leaves unrestricted completeness open.
The left-zero factor fixes the initial variable.  The already certified
`S5_303` calculus can then be replayed behind that fixed initial variable:
its prefix law and interior swap are displayed directly, and its rotation is
exactly the contextual displayed law `xyzy = xzyy`.

The displayed contraction `xxy = xy` removes the temporary initial variable
from both nonsingleton endpoints.  The independent `S5_303` singleton
separator handles the only remaining stratum.  Thus both six-element classes
receive genuine unrestricted endpoints before any quotient adapter is used.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank016.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The displayed `xxy = xy` contracts any repeated nonempty prefix. -/
theorem derivesPrefixContraction (first second : Word Nat) :
    Derives basis ((first ++ first) ++ second) (first ++ second) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The independently certified `S5_303` interior swap is displayed verbatim. -/
theorem derivesInteriorSwap (first second third : Word Nat) :
    Derives basis
      (((first ++ second) ++ third) ++ first)
      (((first ++ third) ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second third)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xyzy = xzyy` rotates behind an unchanged prefix. -/
theorem derivesContextualRotate
    (stem first second : Word Nat) :
    Derives basis
      (((stem ++ first) ++ second) ++ first)
      (((stem ++ second) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 1]) (Word.mk 0 [2, 1, 1]) :=
    Derives.fromBasis (e := law04) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree stem first second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp

/-- Replay the independently complete lower-factor calculus strictly behind a
fixed nonempty prefix, preserving every arbitrary substitution. -/
theorem liftS5_303
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_303.basis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_303.basis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change
          Derives basis
            (stem ++ (Word.mk 0 [1]).bind substitution)
            (stem ++ (Word.mk 0 [0, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesPrefixContraction
              (substitution 0) (substitution 1)).symm
      · change
          Derives basis
            (stem ++ (Word.mk 0 [1, 0]).bind substitution)
            (stem ++ (Word.mk 1 [0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualRotate
            stem (substitution 0) (substitution 1)
      · change
          Derives basis
            (stem ++ (Word.mk 0 [1, 2, 0]).bind substitution)
            (stem ++ (Word.mk 0 [2, 1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesInteriorSwap
              (substitution 0) (substitution 1) (substitution 2))
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction stem substitution)
  | trans _ _ first second =>
      exact (first stem substitution).trans (second stem substitution)
  | prepend left _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (stem ++ left.bind substitution) substitution
  | appendRight _ right induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (induction stem substitution) (right.bind substitution)
  | subst _ next induction =>
      simpa [bind_bind] using
        induction stem (fun letter => (next letter).bind substitution)

/-- Recover the elementary tail characterization from the reviewed terminal
split theorem without unfolding or depending on its private recursion. -/
private theorem singleton_iff_tail_nil (word : Word Nat) :
    SemigroupBasis.CoRoots.S5_83.IsSingletonWord word ↔
      word.tail = [] := by
  have rendered :=
    SemigroupBasis.CoRoots.S5_83.terminalSplit_renderList word
  cases decomposition :
      SemigroupBasis.CoRoots.S5_83.terminalSplit word with
  | singleton final =>
      rw [decomposition] at rendered
      have lengths := congrArg List.length rendered
      simp only [SemigroupBasis.CoRoots.S5_83.TerminalSplit.renderList,
        Word.toList, List.length_cons, List.length_nil] at lengths
      have tailLength : word.tail.length = 0 := by omega
      have tailNil : word.tail = [] := by
        cases tail : word.tail with
        | nil =>
            rfl
        | cons first rest =>
            rw [tail] at tailLength
            simp at tailLength
      simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
        decomposition, tailNil]
  | pair stem penultimate final =>
      rw [decomposition] at rendered
      have tailNonempty : word.tail ≠ [] := by
        intro tailNil
        have lengths := congrArg List.length rendered
        simp only [SemigroupBasis.CoRoots.S5_83.TerminalSplit.renderList,
          Word.toList, List.length_append, List.length_cons,
          List.length_nil, tailNil] at lengths
        omega
      simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
        decomposition, tailNonempty]

/-- Validity in the exact left-zero factor fixes the initial variable. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change identity.SatisfiedBy leftZeroTwo.semigroup at valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

/-- Independent unrestricted completeness: replay the genuine lower-factor
proof behind the fixed head and erase both temporary prefixes. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftValid_head identity leftValid
  have rightCatalogueValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_303.table.semigroup := by
    simpa [rightTable] using rightValid
  have lowerDerivation :=
    SemigroupBasis.CoRoots.S5_303.representative_basis.2
      identity rightCatalogueValid
  have singleton :=
    SemigroupBasis.CoRoots.S5_303.valid_singleton
      identity rightCatalogueValid
  cases identity with
  | mk left right =>
      cases left with
      | mk head leftTail =>
          cases right with
          | mk rightHead rightTail =>
              change head = rightHead at heads
              subst rightHead
              rw [singleton_iff_tail_nil,
                singleton_iff_tail_nil] at singleton
              cases leftTail with
              | nil =>
                  have rightEmpty : rightTail = [] := singleton.mp rfl
                  subst rightTail
                  exact Derives.refl _
              | cons first rest =>
                  have rightNonempty : rightTail ≠ [] := by
                    intro rightEmpty
                    have impossible : first :: rest = [] :=
                      singleton.mpr rightEmpty
                    cases impossible
                  cases rightTail with
                  | nil =>
                      exact False.elim (rightNonempty rfl)
                  | cons other others =>
                      have lifted :=
                        liftS5_303 lowerDerivation
                          (Word.singleton head) Word.singleton
                      rw [bind_singleton, bind_singleton] at lifted
                      have leftCollapse :=
                        derivesPrefixContraction
                          (Word.singleton head) (Word.mk first rest)
                      have rightCollapse :=
                        derivesPrefixContraction
                          (Word.singleton head) (Word.mk other others)
                      simpa [Word.append, Word.singleton,
                        Word.append_assoc] using
                        leftCollapse.symm.trans
                          (lifted.trans rightCollapse)

/-- Construct the reviewed pair structure only after unrestricted proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Package the completed pair theorem as a reusable certified seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_10475_representative_basis :
    BasisFor S6_10475.table.semigroup basis :=
  S6_10475.representative_basis_of_normalizer normalizer

theorem s6_10475_opposite_basis :
    BasisFor S6_10475.table.semigroup.opposite (reversedBasis basis) :=
  S6_10475.opposite_basis_of_normalizer normalizer

theorem s6_7184_representative_basis :
    BasisFor S6_7184.table.semigroup basis :=
  S6_7184.representative_basis_of_normalizer normalizer

theorem s6_7184_opposite_basis :
    BasisFor S6_7184.table.semigroup.opposite (reversedBasis basis) :=
  S6_7184.opposite_basis_of_normalizer normalizer

/-- Reuse the kernel-reviewed transport without manufacturing a factor-theory
implication or omitting any displayed-law derivation. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank016.Seed

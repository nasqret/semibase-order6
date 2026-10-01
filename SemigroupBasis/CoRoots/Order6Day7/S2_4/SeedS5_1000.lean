import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank005
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_1000Family

/-!
# An unrestricted `S2_4 × S5_1000` family seed

The direct `S5_1000` factor is not interchangeable with its opposite: the
opposite seed's `xxy = xyx` already fails on this exact direct table. Instead,
the independently complete direct four-law basis is replayed behind an
arbitrary nonempty context. Its head-changing prefix swap is recovered from
the authenticated eighteen-law presentation by expanding the common initial
block three times, moving one copy past the middle, swapping against the
returning copy, and contracting again.

The genuine final-marker embedding separates singleton words from all longer
words. For the remaining identities, the actual left-zero factor fixes their
common head and the displayed fourth-power expansion removes the temporary
three-copy context. Thus unrestricted intersection completeness is established
before constructing either quotient normalizers or unconditional endpoints.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank005.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | marker + 3 => Word.singleton (marker + 3)

/-- The displayed `xx = xxxxx` expands any nonempty repeated block. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis
      (first ++ first)
      ((((first ++ first) ++ first) ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xxxxy = xy` inserts exactly three initial copies. -/
theorem derivesPrefixExpansion (first final : Word Nat) :
    Derives basis
      (first ++ final)
      ((((first ++ first) ++ first) ++ first) ++ final) := by
  have primitive :
      Derives basis
        (Word.mk 0 [1]) (Word.mk 0 [0, 0, 0, 1]) :=
    (Derives.fromBasis (e := law01) (by simp [basis])).symm
  have substituted :=
    Derives.subst primitive (instantiateThree first final final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xxyz = xyxz` moves one repeated initial block right. -/
theorem derivesInternalHeadExchange
    (first middle final : Word Nat) :
    Derives basis
      (((first ++ first) ++ middle) ++ final)
      (((first ++ middle) ++ first) ++ final) := by
  have primitive :
      Derives basis
        (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 0, 2]) :=
    Derives.fromBasis (e := law07) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first middle final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xyzx = xzyx` swaps blocks before a returning head. -/
theorem derivesReturnSwap
    (first middle final : Word Nat) :
    Derives basis
      (((first ++ middle) ++ final) ++ first)
      (((first ++ final) ++ middle) ++ first) := by
  have primitive :
      Derives basis
        (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) :=
    Derives.fromBasis (e := law09) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first middle final)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Replay the lower factor's head-changing `xyz = yxz` behind a fixed
context without assuming any implication to the opposite factor. -/
theorem derivesContextualPrefixSwap
    (stem first second final : Word Nat) :
    Derives basis
      (((stem ++ first) ++ second) ++ final)
      (((stem ++ second) ++ first) ++ final) := by
  have expand :
      Derives basis
        (((stem ++ first) ++ second) ++ final)
        ((((((stem ++ stem) ++ stem) ++ stem) ++ first) ++ second) ++ final) := by
    simpa [Word.append_assoc] using
      derivesPrefixExpansion stem ((first ++ second) ++ final)
  have move :
      Derives basis
        ((((((stem ++ stem) ++ stem) ++ stem) ++ first) ++ second) ++ final)
        ((((((stem ++ stem) ++ stem) ++ first) ++ second) ++ stem) ++ final) := by
    simpa [Word.append_assoc] using
      derivesInternalHeadExchange stem
        (((stem ++ stem) ++ first) ++ second) final
  have switch :
      Derives basis
        ((((((stem ++ stem) ++ stem) ++ first) ++ second) ++ stem) ++ final)
        ((((((stem ++ stem) ++ stem) ++ second) ++ first) ++ stem) ++ final) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (Derives.prepend (stem ++ stem)
          (derivesReturnSwap stem first second))
        final
  have returnHead :
      Derives basis
        ((((((stem ++ stem) ++ stem) ++ second) ++ first) ++ stem) ++ final)
        ((((((stem ++ stem) ++ stem) ++ stem) ++ second) ++ first) ++ final) := by
    simpa [Word.append_assoc] using
      (derivesInternalHeadExchange stem
        (((stem ++ stem) ++ second) ++ first) final).symm
  have contract :
      Derives basis
        ((((((stem ++ stem) ++ stem) ++ stem) ++ second) ++ first) ++ final)
        (((stem ++ second) ++ first) ++ final) := by
    simpa [Word.append_assoc] using
      (derivesPrefixExpansion stem ((second ++ first) ++ final)).symm
  exact expand.trans <|
    move.trans <| switch.trans <| returnHead.trans contract

/-- Prefixing the displayed `xxyy = xyyx` recovers the exact lower
`xxxyy = xxyyx` law. -/
theorem derivesFinalMove (first second : Word Nat) :
    Derives basis
      ((((first ++ first) ++ first) ++ second) ++ second)
      ((((first ++ first) ++ second) ++ second) ++ first) := by
  have primitive :
      Derives basis
        (Word.mk 0 [0, 1, 1]) (Word.mk 0 [1, 1, 0]) :=
    Derives.fromBasis (e := law05) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using Derives.prepend first substituted

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

/-- Replay every independently certified direct `S5_1000` consequence
strictly behind an arbitrary nonempty initial context. -/
theorem liftS5_1000
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_1000.basis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_1000.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · change Derives basis
          (stem ++ (Word.mk 0 [0]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0, 0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesPowerExpansion (substitution 0))
      · change Derives basis
          (stem ++ (Word.mk 0 [1]).bind substitution)
          (stem ++ (Word.mk 0 [0, 0, 0, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesPrefixExpansion
              (substitution 0) (substitution 1))
      · change Derives basis
          (stem ++ (Word.mk 0 [1, 2]).bind substitution)
          (stem ++ (Word.mk 1 [0, 2]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualPrefixSwap stem
            (substitution 0) (substitution 1) (substitution 2)
      · change Derives basis
          (stem ++ (Word.mk 0 [0, 0, 1, 1]).bind substitution)
          (stem ++ (Word.mk 0 [0, 1, 1, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesFinalMove
              (substitution 0) (substitution 1))
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

private theorem finalMarkerZeroFold (tail : List Nat) :
    tail.foldl
      (fun current (_ : Nat) =>
        finalMarkerThree.semigroup.mul current (1 : Fin 3))
      (0 : Fin 3) = (0 : Fin 3) := by
  induction tail with
  | nil =>
      rfl
  | cons first rest induction =>
      simpa [finalMarkerThree, finalMarkerThreeMul,
        FiniteTable.semigroup] using induction

/-- The actual final-marker factor distinguishes singleton words by one
constant valuation; this is unrestricted semantic evidence. -/
theorem finalMarkerSingletonSeparator (word : Word Nat) :
    finalMarkerThree.semigroup.eval (fun _ => (1 : Fin 3)) word =
        (1 : Fin 3) ↔
      word.tail = [] := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Semigroup.eval]
      | cons first rest =>
          change
            rest.foldl
                (fun current (_ : Nat) =>
                  finalMarkerThree.semigroup.mul current (1 : Fin 3))
                (finalMarkerThree.semigroup.mul (1 : Fin 3) (1 : Fin 3)) =
                (1 : Fin 3) ↔
              first :: rest = []
          change
            rest.foldl
                (fun current (_ : Nat) =>
                  finalMarkerThree.semigroup.mul current (1 : Fin 3))
                (0 : Fin 3) =
                (1 : Fin 3) ↔
              first :: rest = []
          rw [finalMarkerZeroFold]
          exact iff_of_false (by decide) (by simp)

/-- Pull back along the independently reviewed direct-table final-marker
embedding; no finite displayed-law check supplies this implication. -/
theorem rightValid_tail_nil_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightTable.semigroup) :
    identity.lhs.tail = [] ↔ identity.rhs.tail = [] := by
  have directValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1000.table.semigroup := by
    simpa [rightTable] using valid
  have markerValid :=
    SemigroupBasis.CoRoots.S5_1000FamilyInvariant.S5_1000.finalMarkerEmbedding.pullback_identity
      identity directValid
  have evaluated := markerValid (fun _ => (1 : Fin 3))
  constructor
  · intro leftSingleton
    apply (finalMarkerSingletonSeparator identity.rhs).mp
    rw [← evaluated]
    exact (finalMarkerSingletonSeparator identity.lhs).mpr leftSingleton
  · intro rightSingleton
    apply (finalMarkerSingletonSeparator identity.lhs).mp
    rw [evaluated]
    exact (finalMarkerSingletonSeparator identity.rhs).mpr rightSingleton

/-- Validity in the actual `S2_4` left-zero factor fixes the initial
variable, independently of the right-factor presentation. -/
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

/-- Independently unrestricted completeness for the exact eighteen-law
presentation, including the singleton and non-singleton strata. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftValid_head identity leftValid
  have singletonIff := rightValid_tail_nil_iff identity rightValid
  have directValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1000.table.semigroup := by
    simpa [rightTable] using rightValid
  have lower :=
    SemigroupBasis.CoRoots.S5_1000Family.S5_1000.basisFor.2
      identity directValid
  rcases identity with
    ⟨⟨leftHead, leftTail⟩, ⟨rightHead, rightTail⟩⟩
  change leftHead = rightHead at heads
  change leftTail = [] ↔ rightTail = [] at singletonIff
  subst rightHead
  cases leftTail with
  | nil =>
      have rightNil : rightTail = [] := singletonIff.mp rfl
      subst rightTail
      exact Derives.refl _
  | cons leftSecond leftRest =>
      cases rightTail with
      | nil =>
          have impossible : leftSecond :: leftRest = [] :=
            singletonIff.mpr rfl
          simp at impossible
      | cons rightSecond rightRest =>
          let fixed := Word.singleton leftHead
          let leftSuffix : Word Nat := ⟨leftSecond, leftRest⟩
          let rightSuffix : Word Nat := ⟨rightSecond, rightRest⟩
          let triple := (fixed ++ fixed) ++ fixed
          let quadruple := ((fixed ++ fixed) ++ fixed) ++ fixed
          have lifted :=
            liftS5_1000 lower triple Word.singleton
          rw [bind_singleton, bind_singleton] at lifted
          have prefixed :
              Derives basis
                (quadruple ++ leftSuffix)
                (quadruple ++ rightSuffix) := by
            simpa [fixed, leftSuffix, rightSuffix, triple, quadruple,
              Word.singleton, Word.append, Word.append_assoc] using lifted
          have leftExpanded :
              Derives basis
                (Word.mk leftHead (leftSecond :: leftRest))
                (quadruple ++ leftSuffix) := by
            simpa [fixed, leftSuffix, quadruple,
              Word.singleton, Word.append] using
              derivesPrefixExpansion fixed leftSuffix
          have rightExpanded :
              Derives basis
                (Word.mk leftHead (rightSecond :: rightRest))
                (quadruple ++ rightSuffix) := by
            simpa [fixed, rightSuffix, quadruple,
              Word.singleton, Word.append] using
              derivesPrefixExpansion fixed rightSuffix
          exact leftExpanded.trans (prefixed.trans rightExpanded.symm)

/-- Package the pair only after its genuine unrestricted completeness proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable direct-factor rank-005 seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_14907_representative_basis :
    BasisFor S6_14907.table.semigroup basis :=
  S6_14907.representative_basis_of_normalizer normalizer

theorem s6_14907_opposite_basis :
    BasisFor S6_14907.table.semigroup.opposite (reversedBasis basis) :=
  S6_14907.opposite_basis_of_normalizer normalizer

/-- Reviewed transport still requires each displayed-law derivation and both
independent, unrestricted target-factor theory implications. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank005.Seed

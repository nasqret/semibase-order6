import SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank037
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_110Family

/-!
# An unrestricted `S2_4 × S5_110` family seed

The staged rank-037 shell supplies finite soundness and its exact
split-subdirect maps, but does not supply unrestricted completeness.  The
complete `S5_110` calculus has three laws.  Its power and left-fold laws are
displayed verbatim, while its right-fold law is replayed behind any fixed
prefix by combining the displayed left fold with `xyyz = xzyy`.

If the initial variable is repeated, the displayed power and fold laws insert
one extra copy of it, so the entire independently certified lower-factor proof
can be replayed behind that copy.  If the initial variable is simple, the
already reviewed identity element of the exact `S5_110` monoid removes it
semantically, yielding a genuine valid tail identity and a direct contextual
replay.  Neither argument infers unrestricted separation from finite tables.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank037.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The displayed `xx = xxx` expands any nonempty repeated block. -/
theorem derivesPowerExpansion (first : Word Nat) :
    Derives basis (first ++ first) ((first ++ first) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first first first)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xxy = xyx` moves one repeated initial block. -/
theorem derivesLeftFold (first second : Word Nat) :
    Derives basis
      ((first ++ first) ++ second)
      ((first ++ second) ++ first) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1]) (Word.mk 0 [1, 0]) :=
    Derives.fromBasis (e := law01) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree first second second)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The displayed `xyyz = xzyy` transports a repeated block in context. -/
theorem derivesSquareShuttle
    (stem repeated other : Word Nat) :
    Derives basis
      (((stem ++ repeated) ++ repeated) ++ other)
      (((stem ++ other) ++ repeated) ++ repeated) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 1, 2]) (Word.mk 0 [2, 1, 1]) :=
    Derives.fromBasis (e := law02) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree stem repeated other)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Replay the only lower-factor law that changes its own initial variable
while preserving an external nonempty prefix. -/
theorem derivesContextualRightFold
    (stem first second : Word Nat) :
    Derives basis
      (stem ++ ((first ++ second) ++ first))
      (stem ++ ((second ++ first) ++ first)) := by
  have gather :
      Derives basis
        (stem ++ ((first ++ second) ++ first))
        (((stem ++ first) ++ first) ++ second) := by
    simpa [Word.append_assoc] using
      Derives.prepend stem (derivesLeftFold first second).symm
  have shuttle := derivesSquareShuttle stem first second
  simpa [Word.append_assoc] using gather.trans shuttle

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

/-- Replay the independently complete cap-two singleton-order calculus
strictly behind a fixed nonempty prefix. -/
theorem liftS5_110
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_110.basis left right)
    (stem : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (stem ++ left.bind substitution)
      (stem ++ right.bind substitution) := by
  induction derivation generalizing stem substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_110.basis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · change
          Derives basis
            (stem ++ (Word.mk 0 [0]).bind substitution)
            (stem ++ (Word.mk 0 [0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesPowerExpansion (substitution 0))
      · change
          Derives basis
            (stem ++ (Word.mk 0 [1, 0]).bind substitution)
            (stem ++ (Word.mk 0 [0, 1]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend stem
            (derivesLeftFold
              (substitution 0) (substitution 1)).symm
      · change
          Derives basis
            (stem ++ (Word.mk 0 [1, 0]).bind substitution)
            (stem ++ (Word.mk 1 [0, 0]).bind substitution)
        simpa [Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesContextualRightFold
            stem (substitution 0) (substitution 1)
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

private theorem split_at_member
    {letter : Nat} {letters : List Nat}
    (member : letter ∈ letters) :
    ∃ before after : List Nat,
      letters = before ++ letter :: after := by
  induction letters with
  | nil =>
      simp at member
  | cons first rest induction =>
      rcases List.mem_cons.mp member with equal | remaining
      · subst first
        exact ⟨[], rest, rfl⟩
      · obtain ⟨before, after, split⟩ := induction remaining
        exact ⟨first :: before, after, by simp [split]⟩

/-- A repeated initial variable can be duplicated without changing any other
letter; only the displayed power and left-fold laws are used. -/
theorem derivesDuplicateHead
    (head : Nat) (tail : List Nat)
    (repeated : head ∈ tail) :
    Derives basis
      (Word.mk head tail)
      (Word.mk head (head :: tail)) := by
  obtain ⟨before, after, split⟩ := split_at_member repeated
  subst tail
  cases before with
  | nil =>
      have core := derivesPowerExpansion (Word.singleton head)
      cases after with
      | nil =>
          simpa [Word.append, Word.singleton] using core
      | cons final rest =>
          simpa [Word.append, Word.singleton] using
            Derives.appendRight core (Word.mk final rest)
  | cons first middle =>
      let block : Word Nat := ⟨first, middle⟩
      have gather := derivesLeftFold (Word.singleton head) block
      have expand :=
        Derives.appendRight
          (derivesPowerExpansion (Word.singleton head)) block
      have restore :
          Derives basis
            (((Word.singleton head ++ Word.singleton head) ++
                Word.singleton head) ++ block)
            (Word.singleton head ++
              ((Word.singleton head ++ block) ++
                Word.singleton head)) := by
        simpa [Word.append_assoc] using
          Derives.prepend (Word.singleton head) gather
      have core := gather.symm.trans (expand.trans restore)
      have coreWord :
          Derives basis
            (Word.mk head (first :: (middle ++ [head])))
            (Word.mk head (head :: first :: (middle ++ [head]))) := by
        simpa [block, Word.append, Word.singleton] using core
      cases after with
      | nil =>
          exact coreWord
      | cons final rest =>
          have appended :=
            Derives.appendRight coreWord (Word.mk final rest)
          change
            Derives basis
              (Word.mk head
                ((first :: (middle ++ [head])) ++ (final :: rest)))
              (Word.mk head
                ((head :: first :: (middle ++ [head])) ++
                  (final :: rest))) at appended
          simpa [List.append_assoc] using appended

private theorem eval_fold_congr
    {A : Type u}
    (semigroup : Semigroup A)
    (first second : Nat → A) :
    ∀ (letters : List Nat) (initial : A),
      (∀ letter, letter ∈ letters → first letter = second letter) →
        letters.foldl
            (fun current letter => semigroup.mul current (first letter))
            initial =
          letters.foldl
            (fun current letter => semigroup.mul current (second letter))
            initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (by simp)]
      exact eval_fold_congr semigroup first second rest
        (semigroup.mul initial (second letter))
        (fun selected member =>
          agree selected (List.mem_cons.mpr (Or.inr member)))

private theorem eval_congr_on
    {A : Type u}
    (semigroup : Semigroup A)
    (first second : Nat → A) (word : Word Nat)
    (agree :
      ∀ letter, letter ∈ word.toList →
        first letter = second letter) :
    semigroup.eval first word = semigroup.eval second word := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun current letter =>
              semigroup.mul current (first letter))
            (first head) =
          tail.foldl
            (fun current letter =>
              semigroup.mul current (second letter))
            (second head)
      rw [agree head (by simp [Word.toList])]
      exact eval_fold_congr semigroup first second tail (second head)
        (fun letter member =>
          agree letter (by simp [Word.toList, member]))

/-- The exact reviewed lower-factor identity element removes a globally
simple initial variable from a valid identity. -/
theorem rightValidTail_of_simpleHead
    (head : Nat) (left right : Word Nat)
    (leftAbsent : head ∉ left.toList)
    (rightAbsent : head ∉ right.toList)
    (valid :
      (Identity.mk
        (Word.singleton head ++ left)
        (Word.singleton head ++ right)).SatisfiedBy
          rightTable.semigroup) :
    (Identity.mk left right).SatisfiedBy rightTable.semigroup := by
  intro valuation
  let extended : Nat → Fin 5 :=
    fun letter => if letter = head then 4 else valuation letter
  have evaluated := valid extended
  simp only [Semigroup.eval_append,
    Semigroup.eval_singleton] at evaluated
  have extendedHead : extended head = 4 := by
    simp [extended]
  rw [extendedHead] at evaluated
  have leftIdentity (value : Fin 5) :
      rightTable.semigroup.mul (4 : Fin 5) value = value := by
    simpa [rightTable] using
      (SemigroupBasis.CoRoots.S5_110Invariant.s5_110_element_five_identity
        value).1
  rw [leftIdentity, leftIdentity] at evaluated
  have leftUnchanged :
      rightTable.semigroup.eval extended left =
        rightTable.semigroup.eval valuation left := by
    apply eval_congr_on
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact leftAbsent member
    simp [extended, different]
  have rightUnchanged :
      rightTable.semigroup.eval extended right =
        rightTable.semigroup.eval valuation right := by
    apply eval_congr_on
    intro letter member
    have different : letter ≠ head := by
      intro equal
      subst letter
      exact rightAbsent member
    simp [extended, different]
  exact leftUnchanged.symm.trans (evaluated.trans rightUnchanged)

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

/-- Independent unrestricted completeness for the exact three displayed laws.
The globally simple and repeated initial-letter strata are handled separately. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := leftValid_head identity leftValid
  have rightCatalogueValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
    simpa [rightTable] using rightValid
  have lowerDerivation :=
    SemigroupBasis.CoRoots.S5_110Family.S5_110.basisFor.2
      identity rightCatalogueValid
  have signature :=
    SemigroupBasis.CoRoots.S5_110Family.S5_110.valid_sameSignature
      identity rightCatalogueValid
  cases identity with
  | mk left right =>
      cases left with
      | mk head leftTail =>
          cases right with
          | mk rightHead rightTail =>
              change head = rightHead at heads
              subst rightHead
              by_cases repeated : head ∈ leftTail
              · have leftMultiple :
                    2 ≤ (Word.mk head leftTail).toList.count head := by
                  have positive := List.count_pos_iff.mpr repeated
                  simp only [Word.toList, List.count_cons_self]
                  omega
                have rightMultiple :
                    2 ≤ (Word.mk head rightTail).toList.count head :=
                  (signature.multiple head).mp leftMultiple
                have rightRepeated : head ∈ rightTail := by
                  apply List.count_pos_iff.mp
                  simp only [Word.toList,
                    List.count_cons_self] at rightMultiple
                  omega
                have lifted :=
                  liftS5_110 lowerDerivation
                    (Word.singleton head) Word.singleton
                rw [bind_singleton, bind_singleton] at lifted
                have leftDuplicate :=
                  derivesDuplicateHead head leftTail repeated
                have rightDuplicate :=
                  derivesDuplicateHead head rightTail rightRepeated
                simpa [Word.append, Word.singleton] using
                  leftDuplicate.trans (lifted.trans rightDuplicate.symm)
              · have leftCount :
                    (Word.mk head leftTail).toList.count head = 1 := by
                  have zero : leftTail.count head = 0 := by
                    apply Nat.eq_zero_of_not_pos
                    intro positive
                    exact repeated (List.count_pos_iff.mp positive)
                  simp [Word.toList, zero]
                have rightCount :
                    (Word.mk head rightTail).toList.count head = 1 :=
                  (signature.simple head).mp leftCount
                have rightAbsent : head ∉ rightTail := by
                  intro member
                  have positive := List.count_pos_iff.mpr member
                  simp only [Word.toList,
                    List.count_cons_self] at rightCount
                  omega
                cases leftTail with
                | nil =>
                    cases rightTail with
                    | nil =>
                        exact Derives.refl _
                    | cons rightFirst rightRest =>
                        have firstHead : rightFirst = head := by
                          have member :=
                            (signature.support rightFirst).mpr
                              (by simp [Word.toList])
                          simpa [Word.toList] using member
                        exact False.elim
                          (rightAbsent (by simp [firstHead]))
                | cons leftFirst leftRest =>
                    cases rightTail with
                    | nil =>
                        have firstHead : leftFirst = head := by
                          have member :=
                            (signature.support leftFirst).mp
                              (by simp [Word.toList])
                          simpa [Word.toList] using member
                        exact False.elim
                          (repeated (by simp [firstHead]))
                    | cons rightFirst rightRest =>
                        let leftSuffix : Word Nat :=
                          ⟨leftFirst, leftRest⟩
                        let rightSuffix : Word Nat :=
                          ⟨rightFirst, rightRest⟩
                        have leftMissing :
                            head ∉ leftSuffix.toList := by
                          simpa [leftSuffix, Word.toList] using repeated
                        have rightMissing :
                            head ∉ rightSuffix.toList := by
                          simpa [rightSuffix, Word.toList] using rightAbsent
                        have prefixedValid :
                            (Identity.mk
                              (Word.singleton head ++ leftSuffix)
                              (Word.singleton head ++ rightSuffix)).SatisfiedBy
                                rightTable.semigroup := by
                          simpa [leftSuffix, rightSuffix,
                            Word.singleton, Word.append] using rightValid
                        have suffixValid :=
                          rightValidTail_of_simpleHead head
                            leftSuffix rightSuffix
                            leftMissing rightMissing prefixedValid
                        have catalogueSuffixValid :
                            (Identity.mk leftSuffix rightSuffix).SatisfiedBy
                              SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup := by
                          simpa [rightTable] using suffixValid
                        have suffixDerivation :=
                          SemigroupBasis.CoRoots.S5_110Family.S5_110.basisFor.2
                            (Identity.mk leftSuffix rightSuffix)
                            catalogueSuffixValid
                        have lifted :=
                          liftS5_110 suffixDerivation
                            (Word.singleton head) Word.singleton
                        rw [bind_singleton, bind_singleton] at lifted
                        simpa [leftSuffix, rightSuffix,
                          Word.singleton, Word.append] using lifted

/-- Build the reviewed pair structure only after unrestricted completeness. -/
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

theorem s6_3839_representative_basis :
    BasisFor S6_3839.table.semigroup basis :=
  S6_3839.representative_basis_of_normalizer normalizer

theorem s6_3839_opposite_basis :
    BasisFor S6_3839.table.semigroup.opposite (reversedBasis basis) :=
  S6_3839.opposite_basis_of_normalizer normalizer

/-- Reuse kernel-reviewed transport only with genuine displayed-law
derivations and explicit unrestricted factor-theory implications. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank037.Seed

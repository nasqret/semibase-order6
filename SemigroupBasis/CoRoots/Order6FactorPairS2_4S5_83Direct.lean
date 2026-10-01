import SemigroupBasis.CoRoots.S5_83Family
import SemigroupBasis.Generated.Order6OneLocalFordLast.MotifAdapters
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Generated.S3_15
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Subdirect

/-!
# Direct fixed-head intersection of `S2_4`/`S3_15` with `S5_83`/`S5_84`

The exact displayed system with hash prefix `93a811f26898d3d0` cannot derive
the head-changing `S5_83` rotation `xyx = yxx`: its left-zero factor forbids
that identity.  It does derive the rotation below after an arbitrary nonempty
prefix.  This is the local replacement needed to reuse the `S5_83`
normalization theory while preserving the first variable.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Direct

open SemigroupBasis
open SemigroupBasis.Generated.Order6OneLocalFordLast.MotifAdapters
open Sigma_93a811f26898d3d0

private def substituteTwo
    (first second : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | n + 2 => Word.singleton (n + 2)

private def substituteThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/--
The head-guarded rotation `zxyx = zyxx`.

The six intermediate rewrites are
```
zxyx
= zxxyx
= zxzyx
= zxzyzy
= zzyxzy
= zyxzy
= zyxx.
```
-/
theorem guardedRotate
    (guard left middle : Word Nat) :
    Derives basis
      (((guard ++ left) ++ middle) ++ left)
      (((guard ++ middle) ++ left) ++ left) := by
  have step1Base :=
    OneLocalFordLast.DerivedLaw.instantiate
      count_change_binaryLaw2
      (substituteTwo left middle)
  change
    Derives basis
      (((left ++ left) ++ middle) ++ left)
      ((left ++ middle) ++ left) at step1Base
  have step1 :
      Derives basis
        (((guard ++ left) ++ middle) ++ left)
        ((((guard ++ left) ++ left) ++ middle) ++ left) := by
    simpa [Word.append_assoc] using
      Derives.prepend guard step1Base.symm
  have step2Base :=
    OneLocalFordLast.DerivedLaw.instantiate
      count_change_binaryLaw4
      (substituteTwo guard left)
  change
    Derives basis
      ((guard ++ left) ++ guard)
      ((guard ++ left) ++ left) at step2Base
  have step2 :
      Derives basis
        ((((guard ++ left) ++ left) ++ middle) ++ left)
        ((((guard ++ left) ++ guard) ++ middle) ++ left) := by
    simpa [Word.append_assoc] using
      Derives.appendRight step2Base.symm (middle ++ left)
  have step3Base :=
    OneLocalFordLast.DerivedLaw.instantiate
      count_change_binaryLaw4
      (substituteTwo left (guard ++ middle))
  change
    Derives basis
      ((left ++ (guard ++ middle)) ++ left)
      ((left ++ (guard ++ middle)) ++ (guard ++ middle)) at step3Base
  have step3 :
      Derives basis
        ((((guard ++ left) ++ guard) ++ middle) ++ left)
        (((((guard ++ left) ++ guard) ++ middle) ++ guard) ++ middle) := by
    simpa [Word.append_assoc] using
      Derives.prepend guard step3Base
  have step4Base :=
    OneLocalFordLast.DerivedLaw.instantiate
      balanced_localLaw5
      (substituteThree guard left (guard ++ middle))
  change
    Derives basis
      (((guard ++ left) ++ (guard ++ middle)) ++ guard)
      (((guard ++ (guard ++ middle)) ++ left) ++ guard) at step4Base
  have step4 :
      Derives basis
        (((((guard ++ left) ++ guard) ++ middle) ++ guard) ++ middle)
        (((((guard ++ guard) ++ middle) ++ left) ++ guard) ++ middle) := by
    simpa [Word.append_assoc] using
      Derives.appendRight step4Base middle
  have step5Base :=
    OneLocalFordLast.DerivedLaw.instantiate
      count_change_binaryLaw2
      (substituteTwo guard (middle ++ left))
  change
    Derives basis
      (((guard ++ guard) ++ (middle ++ left)) ++ guard)
      ((guard ++ (middle ++ left)) ++ guard) at step5Base
  have step5 :
      Derives basis
        (((((guard ++ guard) ++ middle) ++ left) ++ guard) ++ middle)
        ((((guard ++ middle) ++ left) ++ guard) ++ middle) := by
    simpa [Word.append_assoc] using
      Derives.appendRight step5Base middle
  have step6Base :=
    OneLocalFordLast.DerivedLaw.instantiate
      count_change_binaryLaw4
      (substituteTwo (guard ++ middle) left)
  change
    Derives basis
      (((guard ++ middle) ++ left) ++ (guard ++ middle))
      (((guard ++ middle) ++ left) ++ left) at step6Base
  have step6 :
      Derives basis
        ((((guard ++ middle) ++ left) ++ guard) ++ middle)
        (((guard ++ middle) ++ left) ++ left) := by
    simpa [Word.append_assoc] using
      step6Base
  exact
    step1.trans <|
      step2.trans <|
        step3.trans <|
          step4.trans <|
            step5.trans step6

private theorem derivesPowerExpansion (word : Word Nat) :
    Derives basis
      (word ++ word)
      ((word ++ word) ++ word) := by
  have derivation :=
    OneLocalFordLast.DerivedLaw.instantiate
      powerLaw1 (substituteTwo word word)
  change
    Derives basis
      (word ++ word)
      ((word ++ word) ++ word) at derivation
  exact derivation

private theorem derivesCopy (left right : Word Nat) :
    Derives basis
      ((left ++ right) ++ left)
      ((left ++ right) ++ right) := by
  have derivation :=
    OneLocalFordLast.DerivedLaw.instantiate
      count_change_binaryLaw4
      (substituteTwo left right)
  change
    Derives basis
      ((left ++ right) ++ left)
      ((left ++ right) ++ right) at derivation
  exact derivation

private theorem derivesLongInsertion
    (first second third : Word Nat) :
    Derives basis
      ((first ++ second) ++ third)
      (((first ++ first) ++ second) ++ third) := by
  have derivation :=
    OneLocalFordLast.DerivedLaw.instantiate
      count_change_localLaw3
      (substituteThree first second third)
  change
    Derives basis
      (((first ++ first) ++ second) ++ third)
      ((first ++ second) ++ third) at derivation
  exact derivation.symm

private theorem bindAppend
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bindBind
    (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bindSingleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem prefixedS5AxiomDerivesAfterBind
    (guard : Word Nat) (substitution : Nat → Word Nat)
    (identity : Identity Nat)
    (member :
      identity ∈ SemigroupBasis.CoRoots.S5_83.basis) :
    Derives basis
      (guard ++ identity.lhs.bind substitution)
      (guard ++ identity.rhs.bind substitution) := by
  simp only [SemigroupBasis.CoRoots.S5_83.basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · change
      Derives basis
        (guard ++ (substitution 0 ++ substitution 0))
        (guard ++ ((substitution 0 ++ substitution 0) ++ substitution 0))
    exact Derives.prepend guard
      (derivesPowerExpansion (substitution 0))
  · change
      Derives basis
        (guard ++ ((substitution 0 ++ substitution 1) ++ substitution 0))
        (guard ++ ((substitution 0 ++ substitution 1) ++ substitution 1))
    exact Derives.prepend guard
      (derivesCopy (substitution 0) (substitution 1))
  · change
      Derives basis
        (guard ++ ((substitution 0 ++ substitution 1) ++ substitution 0))
        (guard ++ ((substitution 1 ++ substitution 0) ++ substitution 0))
    simpa [Word.append_assoc] using
      guardedRotate guard (substitution 0) (substitution 1)
  · change
      Derives basis
        (guard ++ ((substitution 0 ++ substitution 1) ++ substitution 2))
        (guard ++
          (((substitution 0 ++ substitution 0) ++ substitution 1) ++
            substitution 2))
    exact Derives.prepend guard
      (derivesLongInsertion
        (substitution 0) (substitution 1) (substitution 2))

/-- Replay an arbitrary `S5_83` derivation behind one fixed nonempty prefix. -/
theorem liftS5DerivationUnderPrefix
    {left right : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_83.basis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (guard ++ left.bind substitution)
      (guard ++ right.bind substitution) := by
  induction derivation generalizing guard substitution with
  | fromBasis member =>
      exact prefixedS5AxiomDerivesAfterBind
        guard substitution _ member
  | refl word =>
      exact Derives.refl _
  | symm derivation ih =>
      exact Derives.symm (ih guard substitution)
  | trans first second ihFirst ihSecond =>
      exact Derives.trans
        (ihFirst guard substitution)
        (ihSecond guard substitution)
  | prepend pre derivation ih =>
      simpa [bindAppend, Word.append_assoc] using
        ih (guard ++ pre.bind substitution) substitution
  | appendRight derivation post ih =>
      simpa [bindAppend, Word.append_assoc] using
        Derives.appendRight
          (ih guard substitution) (post.bind substitution)
  | subst derivation first ih =>
      simpa [bindBind] using
        ih guard
          (fun letter => (first letter).bind substitution)

private theorem singleton_of_tail_nil
    (word : Word Nat) (tail : word.tail = []) :
    SemigroupBasis.CoRoots.S5_83.IsSingletonWord word := by
  cases word with
  | mk head letters =>
      change letters = [] at tail
      subst letters
      change True
      trivial

private theorem tail_nil_of_singleton
    (word : Word Nat)
    (singleton :
      SemigroupBasis.CoRoots.S5_83.IsSingletonWord word) :
    word.tail = [] := by
  have rendered :=
    SemigroupBasis.CoRoots.S5_83.terminalSplit_renderList word
  cases splitEq :
      SemigroupBasis.CoRoots.S5_83.terminalSplit word with
  | singleton final =>
      rw [splitEq] at rendered
      change [final] = word.head :: word.tail at rendered
      injection rendered with _ tails
      exact tails.symm
  | pair stem penultimate final =>
      simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
        splitEq] at singleton

private theorem rigidUniqueTerminalPair
    (word : Word Nat) (final : Nat)
    (tail : word.tail = [final])
    (different : final ≠ word.head) :
    SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
      word word.head final := by
  cases word with
  | mk head letters =>
      change letters = [final] at tail
      subst letters
      have splitEq :
          SemigroupBasis.CoRoots.S5_83.terminalSplit
              ({ head := head, tail := [final] } : Word Nat) =
            SemigroupBasis.CoRoots.S5_83.TerminalSplit.pair [] head final := by
        rfl
      simpa [SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair,
        splitEq] using different

private theorem tail_eq_singleton_of_uniqueTerminalPair_head
    (word : Word Nat) (final : Nat)
    (pair :
      SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
        word word.head final) :
    word.tail = [final] := by
  have rendered :=
    SemigroupBasis.CoRoots.S5_83.terminalSplit_renderList word
  cases splitEq :
      SemigroupBasis.CoRoots.S5_83.terminalSplit word with
  | singleton actualFinal =>
      simp [SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair,
        splitEq] at pair
  | pair stem penultimate actualFinal =>
      have parts :
          penultimate = word.head ∧
            actualFinal = final ∧
            word.head ∉ stem ∧
            final ≠ word.head ∧
            final ∉ stem := by
        simpa [SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair,
          splitEq] using pair
      rw [splitEq] at rendered
      cases stem with
      | nil =>
          change
            [penultimate, actualFinal] =
              word.head :: word.tail at rendered
          rw [parts.1, parts.2.1] at rendered
          injection rendered with _ tails
          exact tails.symm
      | cons first rest =>
          change
            first :: (rest ++ [penultimate, actualFinal]) =
              word.head :: word.tail at rendered
          have firstEq : first = word.head :=
            (List.cons.inj rendered).1
          exact False.elim <| parts.2.2.1 <| by
            rw [← firstEq]
            exact List.Mem.head rest

private theorem duplicateInitialOrRigid
    (word : Word Nat) (nonempty : word.tail ≠ []) :
    Derives basis word (Word.singleton word.head ++ word) ∨
      ∃ final,
        word.tail = [final] ∧ final ≠ word.head := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          exact False.elim (nonempty rfl)
      | cons second rest =>
          cases rest with
          | nil =>
              by_cases equal : second = head
              · subst second
                exact Or.inl <| by
                  simpa [Word.singleton, Word.append] using
                    derivesPowerExpansion (Word.singleton head)
              · exact Or.inr ⟨second, rfl, equal⟩
          | cons third more =>
              let suffix : Word Nat := ⟨third, more⟩
              exact Or.inl <| by
                simpa [suffix, Word.singleton, Word.append] using
                  derivesLongInsertion
                    (Word.singleton head)
                    (Word.singleton second)
                    suffix

private theorem rigidEqOfSignatureAndHead
    {left right : Word Nat} {final : Nat}
    (same :
      SemigroupBasis.CoRoots.S5_83.SameTerminalUniqueSuffixSignature
        left right)
    (heads : left.head = right.head)
    (leftTail : left.tail = [final])
    (different : final ≠ left.head) :
    left = right := by
  have leftPair :=
    rigidUniqueTerminalPair left final leftTail different
  have rightPair :
      SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
        right left.head final :=
    (same.uniqueTerminalPair left.head final).mp leftPair
  have rightPairAtHead :
      SemigroupBasis.CoRoots.S5_83.UniqueTerminalPair
        right right.head final := by
    simpa [heads] using rightPair
  have rightTail :=
    tail_eq_singleton_of_uniqueTerminalPair_head
      right final rightPairAtHead
  apply Word.toList_injective
  simp [Word.toList, leftTail, rightTail, heads]

/-- The exact five-law system is complete for the joint invariant consisting
of the `S5_83` signature and the literal first variable. -/
theorem derivesOfSignatureAndHead
    {left right : Word Nat}
    (same :
      SemigroupBasis.CoRoots.S5_83.SameTerminalUniqueSuffixSignature
        left right)
    (heads : left.head = right.head) :
    Derives basis left right := by
  by_cases leftSingleton :
      SemigroupBasis.CoRoots.S5_83.IsSingletonWord left
  · have rightSingleton := same.singleton.mp leftSingleton
    have leftTail := tail_nil_of_singleton left leftSingleton
    have rightTail := tail_nil_of_singleton right rightSingleton
    have equal : left = right := by
      apply Word.toList_injective
      simp [Word.toList, leftTail, rightTail, heads]
    subst right
    exact Derives.refl _
  · have rightNotSingleton :
        ¬ SemigroupBasis.CoRoots.S5_83.IsSingletonWord right := by
      intro rightSingleton
      exact leftSingleton (same.singleton.mpr rightSingleton)
    have leftNonempty : left.tail ≠ [] := by
      intro tail
      exact leftSingleton (singleton_of_tail_nil left tail)
    have rightNonempty : right.tail ≠ [] := by
      intro tail
      exact rightNotSingleton (singleton_of_tail_nil right tail)
    rcases duplicateInitialOrRigid left leftNonempty with
      leftDuplicate | ⟨leftFinal, leftTail, leftDifferent⟩
    · rcases duplicateInitialOrRigid right rightNonempty with
        rightDuplicate | ⟨rightFinal, rightTail, rightDifferent⟩
      · have sourceDerivation :=
          SemigroupBasis.CoRoots.S5_83.derives_of_sameTerminalUniqueSuffixSignature
            left right same
        have lifted :=
          liftS5DerivationUnderPrefix sourceDerivation
            (Word.singleton left.head) Word.singleton
        rw [bindSingleton, bindSingleton] at lifted
        have guarded :
            Derives basis
              (Word.singleton left.head ++ left)
              (Word.singleton right.head ++ right) := by
          simpa [heads] using lifted
        exact
          leftDuplicate.trans <|
            guarded.trans rightDuplicate.symm
      · have equal :=
          rigidEqOfSignatureAndHead
            same.symm heads.symm rightTail rightDifferent
        subst left
        exact Derives.refl _
    · have equal :=
        rigidEqOfSignatureAndHead
          same heads leftTail leftDifferent
      subst right
      exact Derives.refl _

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem modelsS2_4 :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S2_4.table basis toFinThree (by decide)

theorem modelsS3_15 :
    Models SemigroupBasis.Generated.S3_15.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_15.table basis toFinThree (by decide)

theorem modelsS5_83 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_83.table
    basis toFinThree (by decide)

theorem modelsS5_84 :
    Models
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      basis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S5_84.table
    basis toFinThree (by decide)

private theorem head_eq_of_s2_4_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S2_4.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  change
    SemigroupBasis.Examples.leftZeroTwo.semigroup.eval
        valuation identity.lhs =
      SemigroupBasis.Examples.leftZeroTwo.semigroup.eval
        valuation identity.rhs at evaluated
  rw [SemigroupBasis.Examples.leftZeroTwo_eval,
    SemigroupBasis.Examples.leftZeroTwo_eval] at evaluated
  simp [valuation, different, Ne.symm different] at evaluated

private theorem head_eq_of_s3_15_valid
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_15.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  change
    identity.SatisfiedBy
      SemigroupBasis.Examples.leftNormalBandFifteen.semigroup at valid
  exact
    SemigroupBasis.Examples.leftNormalBandFifteenValid_head_eq
      identity valid

def intersectionS2_4S5_83 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_83
  complete := by
    intro identity initialValid terminalValid
    exact derivesOfSignatureAndHead
      (SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
        identity terminalValid)
      (head_eq_of_s2_4_valid identity initialValid)

def intersectionS2_4S5_84 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      basis where
  leftModels := modelsS2_4
  rightModels := modelsS5_84
  complete := by
    intro identity initialValid terminalValid
    exact derivesOfSignatureAndHead
      (SemigroupBasis.CoRoots.S5_83Factors.S5_84.valid_signature
        identity terminalValid)
      (head_eq_of_s2_4_valid identity initialValid)

def intersectionS3_15S5_83 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      basis where
  leftModels := modelsS3_15
  rightModels := modelsS5_83
  complete := by
    intro identity initialValid terminalValid
    exact derivesOfSignatureAndHead
      (SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
        identity terminalValid)
      (head_eq_of_s3_15_valid identity initialValid)

def intersectionS3_15S5_84 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      basis where
  leftModels := modelsS3_15
  rightModels := modelsS5_84
  complete := by
    intro identity initialValid terminalValid
    exact derivesOfSignatureAndHead
      (SemigroupBasis.CoRoots.S5_83Factors.S5_84.valid_signature
        identity terminalValid)
      (head_eq_of_s3_15_valid identity initialValid)

end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_83Direct

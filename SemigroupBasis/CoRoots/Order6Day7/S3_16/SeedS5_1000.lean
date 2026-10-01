import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank069
import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_353Opposite
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_1000Family
import SemigroupBasis.CoRoots.S5_1149

/-!
# An unrestricted `S3_16 × S5_1000` family seed

Four checked product embeddings identify the actual pair with
`finalMarkerThree × S5_1149` on every alphabet.  The independently complete
two-law `S5_1149` presentation preserves the whole first-occurrence sequence
and every multiplicity modulo three.  Its power and gathering axioms both
lift behind an arbitrary nonempty final guard using literal rank-069 laws.

A globally unique final variable can therefore be stripped from the owner
identity and restored as that guard.  For a repeated final, the frozen laws
first append three copies of the final variable and then use their exact
three-block terminal transfer to replace those copies by three copies of the
common initial variable.  This provides a common guard on both sides even
when their original final variables differ.  The two strata prove genuine
unrestricted completeness before constructing the quotient normalizer or the
two unconditional class endpoints.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank069.Seed

open SemigroupBasis
open SemigroupBasis.Examples

universe u v

abbrev ownerTable : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1149.table

abbrev targetProduct : Semigroup (Fin 3 × Fin 5) :=
  leftTable.semigroup.prod rightTable.semigroup

abbrev ownerProduct : Semigroup (Fin 3 × Fin 5) :=
  finalMarkerThree.semigroup.prod ownerTable.semigroup

/-- Exact one-based target coordinates `[1,2,3,2,2] × [1,3,1,4,5]`. -/
def ownerIntoTargetProduct :
    Embedding ownerTable.semigroup targetProduct where
  toFun := fun value =>
    (if value.val = 0 then 0 else if value.val = 2 then 2 else 1,
      if value.val = 0 then 0 else
        if value.val = 1 then 2 else
          if value.val = 2 then 0 else
            if value.val = 3 then 3 else 4)
  map_mul := by
    intro first second
    apply Prod.ext <;> apply Fin.ext <;> revert first second <;> decide
  injective := by
    intro first second equal
    revert first second
    decide

/-- Exact one-based target coordinates `[1,1,1] × [1,2,3]`. -/
def markerIntoTargetProduct :
    Embedding finalMarkerThree.semigroup targetProduct where
  toFun := fun value => (0, value.castLE (by decide))
  map_mul := by
    intro first second
    apply Prod.ext <;> apply Fin.ext <;> revert first second <;> decide
  injective := by
    intro first second equal
    revert first second
    decide

/-- Exact one-based owner coordinates `[1,1,1] × [1,2,3]`. -/
def targetLeftIntoOwnerProduct :
    Embedding leftTable.semigroup ownerProduct where
  toFun := fun value => (0, value.castLE (by decide))
  map_mul := by
    intro first second
    apply Prod.ext <;> apply Fin.ext <;> revert first second <;> decide
  injective := by
    intro first second equal
    revert first second
    decide

/-- Exact one-based owner coordinates `[1,2,3,3,3] × [1,1,2,4,5]`. -/
def targetRightIntoOwnerProduct :
    Embedding rightTable.semigroup ownerProduct where
  toFun := fun value =>
    (if value.val = 0 then 0 else if value.val = 1 then 1 else 2,
      if value.val = 0 then 0 else
        if value.val = 1 then 0 else
          if value.val = 2 then 1 else
            if value.val = 3 then 3 else 4)
  map_mul := by
    intro first second
    apply Prod.ext <;> apply Fin.ext <;> revert first second <;> decide
  injective := by
    intro first second equal
    revert first second
    decide

/-- Genuine unrestricted identity-theory equality on every alphabet. -/
theorem ownerPairTheory_iff_targetPairTheory
    {α : Type u} (identity : Identity α) :
    (identity.SatisfiedBy leftTable.semigroup ∧
      identity.SatisfiedBy rightTable.semigroup) ↔
      (identity.SatisfiedBy finalMarkerThree.semigroup ∧
        identity.SatisfiedBy ownerTable.semigroup) := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    have product := Identity.satisfiedBy_prod leftValid rightValid
    exact ⟨markerIntoTargetProduct.pullback_identity identity product,
      ownerIntoTargetProduct.pullback_identity identity product⟩
  · rintro ⟨markerValid, ownerValid⟩
    have product := Identity.satisfiedBy_prod markerValid ownerValid
    exact ⟨targetLeftIntoOwnerProduct.pullback_identity identity product,
      targetRightIntoOwnerProduct.pullback_identity identity product⟩

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

/-- Displayed law 00 inserts three copies after an adjacent repeated block. -/
theorem derivesPowerExpansion (block : Word Nat) :
    Derives basis
      (block ++ block)
      ((((block ++ block) ++ block) ++ block) ++ block) := by
  have primitive :
      Derives basis (Word.mk 0 [0]) (Word.mk 0 [0, 0, 0, 0]) :=
    Derives.fromBasis (e := law00) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree block block block)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Displayed law 01 inserts three copies immediately before any guard. -/
theorem derivesPrefixExpansion (block guard : Word Nat) :
    Derives basis
      (block ++ guard)
      ((((block ++ block) ++ block) ++ block) ++ guard) := by
  have primitive :
      Derives basis (Word.mk 0 [1]) (Word.mk 0 [0, 0, 0, 1]) :=
    (Derives.fromBasis (e := law01) (by simp [basis])).symm
  have substituted :=
    Derives.subst primitive (instantiateThree block guard guard)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Displayed law 03 walks one repeated block to the terminal position. -/
theorem derivesRepeatedFinalShift (block middle : Word Nat) :
    Derives basis
      (((block ++ block) ++ middle) ++ block)
      (((block ++ middle) ++ block) ++ block) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 0]) (Word.mk 0 [1, 0, 0]) :=
    Derives.fromBasis (e := law03) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree block middle middle)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Displayed law 07 is exactly the complete owner's guarded gather axiom. -/
theorem derivesGuardedGather (block middle guard : Word Nat) :
    Derives basis
      (((block ++ block) ++ middle) ++ guard)
      (((block ++ middle) ++ block) ++ guard) := by
  have primitive :
      Derives basis (Word.mk 0 [0, 1, 2]) (Word.mk 0 [1, 0, 2]) :=
    Derives.fromBasis (e := law07) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree block middle guard)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Displayed law 14 replaces a final triple by three initial-block copies. -/
theorem derivesInitialFinalTripleTransfer
    (initial middle final : Word Nat) :
    Derives basis
      (((((initial ++ middle) ++ final) ++ initial) ++ initial) ++ initial)
      (((((initial ++ middle) ++ final) ++ final) ++ final) ++ final) := by
  have primitive :
      Derives basis (Word.mk 0 [1, 2, 0, 0, 0])
        (Word.mk 0 [1, 2, 2, 2, 2]) :=
    Derives.fromBasis (e := law14) (by simp [basis])
  have substituted :=
    Derives.subst primitive (instantiateThree initial middle final)
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

private theorem prefixFinal_cons_shape
    (head : Nat) (tail : List Nat) (final : Nat) :
  wordOfPrefixFinal (head :: tail) final =
      Word.mk head (tail ++ [final]) := by
  apply Word.toList_injective
  rw [toList_wordOfPrefixFinal]
  rfl

/-- Replay every unrestricted owner consequence behind any nonempty suffix. -/
theorem liftS5_1149UnderFinalGuard
    {left right : Word Nat}
    (derivation : Derives SemigroupBasis.CoRoots.S5_1149.basis left right)
    (guard : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (left.bind substitution ++ guard)
      (right.bind substitution ++ guard) := by
  induction derivation generalizing guard substitution with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_1149.basis,
        SemigroupBasis.CoRoots.S5_1149.s5_1149Basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [SemigroupBasis.CoRoots.S5_1149.s5_1149PowerLaw,
          SemigroupBasis.CoRoots.S5_1149.s5_1149X,
          SemigroupBasis.CoRoots.S5_1149.s5_1149XXXX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesPrefixExpansion (substitution 0) guard
      · simpa [SemigroupBasis.CoRoots.S5_1149.s5_1149GatherLaw,
          SemigroupBasis.CoRoots.S5_1149.s5_1149XXY,
          SemigroupBasis.CoRoots.S5_1149.s5_1149XYX,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          derivesGuardedGather (substitution 0) (substitution 1) guard
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction guard substitution)
  | trans _ _ first second =>
      exact (first guard substitution).trans (second guard substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution)
          (induction guard substitution)
  | appendRight _ suffix induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (suffix.bind substitution ++ guard) substitution
  | subst _ next induction =>
      simpa [bind_bind] using
        induction guard (fun letter => (next letter).bind substitution)

/-- A separated repeated final accepts three extra copies of itself. -/
theorem derivesSeparatedFinalTriple
    (final middle : Word Nat) :
    Derives basis
      ((final ++ middle) ++ final)
      (((((final ++ middle) ++ final) ++ final) ++ final) ++ final) := by
  have expanded :
      Derives basis
        ((final ++ middle) ++ final)
        (((((final ++ final) ++ final) ++ final) ++ middle) ++ final) := by
    simpa [Word.append_assoc] using
      derivesPrefixExpansion final (middle ++ final)
  have first :
      Derives basis
        (((((final ++ final) ++ final) ++ final) ++ middle) ++ final)
        (((((final ++ final) ++ final) ++ middle) ++ final) ++ final) := by
    simpa [Word.append_assoc] using
      derivesRepeatedFinalShift final ((final ++ final) ++ middle)
  have second :
      Derives basis
        (((((final ++ final) ++ final) ++ middle) ++ final) ++ final)
        (((((final ++ final) ++ middle) ++ final) ++ final) ++ final) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesRepeatedFinalShift final (final ++ middle)) final
  have third :
      Derives basis
        (((((final ++ final) ++ middle) ++ final) ++ final) ++ final)
        (((((final ++ middle) ++ final) ++ final) ++ final) ++ final) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesRepeatedFinalShift final middle) (final ++ final)
  exact expanded.trans (first.trans (second.trans third))

/-- Any globally repeated final variable accepts its period-three tail. -/
theorem derivesAppendRepeatedFinalTriple
    (stem : List Nat) (final : Nat) (repeated : final ∈ stem) :
    Derives basis
      (wordOfPrefixFinal stem final)
      (wordOfPrefixFinal stem final ++
        ((Word.singleton final ++ Word.singleton final) ++
          Word.singleton final)) := by
  induction stem with
  | nil => simp at repeated
  | cons first rest induction =>
      by_cases same : first = final
      · subst first
        cases rest with
        | nil =>
            simpa [wordOfPrefixFinal, Word.singleton, Word.append,
              Word.append_assoc] using
              derivesPowerExpansion (Word.singleton final)
        | cons middle tail =>
            have shape :
                wordOfPrefixFinal (final :: middle :: tail) final =
                  ((Word.singleton final ++ Word.mk middle tail) ++
                    Word.singleton final) := by
              rw [prefixFinal_cons_shape]
              rfl
            rw [shape]
            simpa [Word.append_assoc] using
              derivesSeparatedFinalTriple
                (Word.singleton final) (Word.mk middle tail)
      · have restRepeated : final ∈ rest := by
          simpa [same, Ne.symm same] using repeated
        simpa [wordOfPrefixFinal, Word.append_assoc] using
          Derives.prepend (Word.singleton first)
            (induction restRepeated)

/-- In the nonsimple-final stratum the common head supplies a common guard. -/
theorem derivesAppendInitialTriple_of_repeatedFinal
    (word : Word Nat)
    (repeated : (splitPrefixFinal word).2 ∈ (splitPrefixFinal word).1) :
    Derives basis word
      (word ++ ((Word.singleton word.head ++ Word.singleton word.head) ++
        Word.singleton word.head)) := by
  let final := (splitPrefixFinal word).2
  cases stemShape : (splitPrefixFinal word).1 with
  | nil =>
      have impossible : final ∈ ([] : List Nat) := by
        simp [stemShape] at repeated
      simp at impossible
  | cons first rest =>
      have reconstruct : wordOfPrefixFinal (first :: rest) final = word := by
        simpa [final, stemShape] using wordOfPrefixFinal_split word
      have repeat' : final ∈ first :: rest := by
        simpa [final, stemShape] using repeated
      have headEq : word.head = first := by
        have heads := congrArg Word.head reconstruct
        simpa [wordOfPrefixFinal] using heads.symm
      cases rest with
      | nil =>
          have same : final = first := by simpa using repeat'
          have shape : word = Word.singleton first ++ Word.singleton first := by
            rw [← reconstruct, same]
            rfl
          rw [shape]
          simpa [headEq, Word.singleton, Word.append, Word.append_assoc] using
            derivesPowerExpansion (Word.singleton first)
      | cons middle tail =>
          let headWord := Word.singleton first
          let middleWord := Word.mk middle tail
          let finalWord := Word.singleton final
          have decomposition :
              ((headWord ++ middleWord) ++ finalWord) = word := by
            rw [← reconstruct, prefixFinal_cons_shape]
            rfl
          have finalExpanded :=
            derivesAppendRepeatedFinalTriple (first :: middle :: tail)
              final repeat'
          rw [reconstruct] at finalExpanded
          have expanded :
              Derives basis word
                (word ++ ((finalWord ++ finalWord) ++ finalWord)) := by
            simpa [finalWord] using finalExpanded
          have transferred :
              Derives basis
                (word ++ ((finalWord ++ finalWord) ++ finalWord))
                (word ++ ((headWord ++ headWord) ++ headWord)) := by
            simpa [decomposition, Word.append_assoc] using
              (derivesInitialFinalTripleTransfer
                headWord middleWord finalWord).symm
          simpa [headWord, headEq] using expanded.trans transferred

private theorem foldl_eval_congr
    (semigroup : Semigroup S)
    (first second : Nat → S) :
    ∀ (letters : List Nat) (initial : S),
      (∀ letter, letter ∈ letters → first letter = second letter) →
      letters.foldl (fun value letter => semigroup.mul value (first letter))
          initial =
        letters.foldl (fun value letter => semigroup.mul value (second letter))
          initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply foldl_eval_congr semigroup
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem eval_congr_on_support
    (semigroup : Semigroup S) (first second : Nat → S)
    (word : Word Nat)
    (agree : ∀ letter, letter ∈ word.toList → first letter = second letter) :
    semigroup.eval first word = semigroup.eval second word := by
  cases word with
  | mk head tail =>
      simp only [Semigroup.eval]
      rw [agree head (by simp [Word.toList])]
      apply foldl_eval_congr semigroup
      intro letter member
      exact agree letter (List.Mem.tail head member)

/-- The exact complete owner table is right reductive. -/
theorem ownerRightReductive (first second : Fin 5)
    (equalRows : ∀ marker : Fin 5,
      ownerTable.semigroup.mul first marker =
        ownerTable.semigroup.mul second marker) :
    first = second := by
  revert first second
  decide

/-- A globally fresh final letter can be stripped from the owner validity. -/
theorem ownerStripUniqueFinal
    (final : Nat) (left right : Word Nat)
    (leftAbsent : final ∉ left.toList)
    (rightAbsent : final ∉ right.toList)
    (whole :
      (Identity.mk
        (left ++ Word.singleton final)
        (right ++ Word.singleton final)).SatisfiedBy ownerTable.semigroup) :
    (Identity.mk left right).SatisfiedBy ownerTable.semigroup := by
  intro valuation
  apply ownerRightReductive
  intro marker
  let lifted : Nat → Fin 5 :=
    fun letter => if letter = final then marker else valuation letter
  have leftAgree :
      ownerTable.semigroup.eval valuation left =
        ownerTable.semigroup.eval lifted left := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact leftAbsent member
    simp [lifted, different]
  have rightAgree :
      ownerTable.semigroup.eval valuation right =
        ownerTable.semigroup.eval lifted right := by
    apply eval_congr_on_support
    intro letter member
    have different : letter ≠ final := by
      intro equal
      subst letter
      exact rightAbsent member
    simp [lifted, different]
  have evaluated := whole lifted
  simp only [Semigroup.eval_append, Semigroup.eval_singleton] at evaluated
  have liftedFinal : lifted final = marker := by simp [lifted]
  rw [liftedFinal] at evaluated
  exact
    (congrArg (fun value => ownerTable.semigroup.mul value marker) leftAgree).trans
      (evaluated.trans
        (congrArg (fun value => ownerTable.semigroup.mul value marker)
          rightAgree.symm))

/-- Actual `S3_16` validity fixes the genuine common initial variable. -/
theorem leftValid_head
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  have ordered :=
    SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank018.Seed.firstOccurrences_of_leftValid
      identity valid
  have heads := congrArg (fun letters : List Nat => letters.head?) ordered
  simpa [Word.toList, firstOccurrenceSequence] using heads

/-- Complete unrestricted derivation for the immutable sixteen-law package. -/
theorem derives_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have ownerPair :=
    (ownerPairTheory_iff_targetPairTheory identity).mp
      ⟨leftValid, rightValid⟩
  have markerValid := ownerPair.1
  have ownerValid := ownerPair.2
  have lower :=
    SemigroupBasis.CoRoots.S5_1149.representative_basis.2
      identity ownerValid
  let leftPrefix := (splitPrefixFinal identity.lhs).1
  let leftFinal := (splitPrefixFinal identity.lhs).2
  let rightPrefix := (splitPrefixFinal identity.rhs).1
  let rightFinal := (splitPrefixFinal identity.rhs).2
  have leftReconstruct :
      wordOfPrefixFinal leftPrefix leftFinal = identity.lhs :=
    wordOfPrefixFinal_split identity.lhs
  have rightReconstruct :
      wordOfPrefixFinal rightPrefix rightFinal = identity.rhs :=
    wordOfPrefixFinal_split identity.rhs
  by_cases leftSimple : leftFinal ∉ leftPrefix
  · have rightSimple :
        rightFinal = leftFinal ∧ leftFinal ∉ rightPrefix :=
      (finalMarkerValid_splitSimpleFinal_iff
        identity markerValid leftFinal).mp ⟨rfl, leftSimple⟩
    have finals : rightFinal = leftFinal := rightSimple.1
    have rightAbsent : leftFinal ∉ rightPrefix := rightSimple.2
    have support :=
      SemigroupBasis.CoRoots.S5_196.finalMarkerValid_support
        identity markerValid
    have emptyIff : leftPrefix = [] ↔ rightPrefix = [] := by
      constructor
      · intro empty
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have rightMember : letter ∈ identity.rhs.toList := by
          rw [← rightReconstruct, toList_wordOfPrefixFinal]
          exact List.mem_append_left _ member
        have leftMember := (support letter).mpr rightMember
        rw [← leftReconstruct, toList_wordOfPrefixFinal, empty] at leftMember
        have same : letter = leftFinal := by simpa using leftMember
        subst letter
        exact rightAbsent member
      · intro empty
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have leftMember : letter ∈ identity.lhs.toList := by
          rw [← leftReconstruct, toList_wordOfPrefixFinal]
          exact List.mem_append_left _ member
        have rightMember := (support letter).mp leftMember
        rw [← rightReconstruct, toList_wordOfPrefixFinal, empty] at rightMember
        have same : letter = rightFinal := by simpa using rightMember
        rw [finals] at same
        subst letter
        exact leftSimple member
    cases leftShape : leftPrefix with
    | nil =>
        have rightEmpty : rightPrefix = [] := emptyIff.mp leftShape
        have equality : identity.lhs = identity.rhs := by
          rw [← leftReconstruct, ← rightReconstruct,
            leftShape, rightEmpty, finals]
        rw [equality]
        exact Derives.refl _
    | cons leftHead leftTail =>
        cases rightShape : rightPrefix with
        | nil =>
            have contradiction := emptyIff.mpr rightShape
            rw [leftShape] at contradiction
            simp at contradiction
        | cons rightHead rightTail =>
            let leftWord : Word Nat := Word.mk leftHead leftTail
            let rightWord : Word Nat := Word.mk rightHead rightTail
            have leftWordReconstruct :
                leftWord ++ Word.singleton leftFinal = identity.lhs := by
              apply Word.toList_injective
              rw [Word.toList_append, Word.toList_singleton,
                ← leftReconstruct, toList_wordOfPrefixFinal, leftShape]
              rfl
            have rightWordReconstruct :
                rightWord ++ Word.singleton leftFinal = identity.rhs := by
              apply Word.toList_injective
              rw [Word.toList_append, Word.toList_singleton,
                ← rightReconstruct, toList_wordOfPrefixFinal,
                rightShape, finals]
              rfl
            have leftAbsentWord : leftFinal ∉ leftWord.toList := by
              simpa [leftWord, Word.toList, leftShape] using leftSimple
            have rightAbsentWord : leftFinal ∉ rightWord.toList := by
              simpa [rightWord, Word.toList, rightShape] using rightAbsent
            have whole :
                (Identity.mk
                  (leftWord ++ Word.singleton leftFinal)
                  (rightWord ++ Word.singleton leftFinal)).SatisfiedBy
                    ownerTable.semigroup := by
              simpa [leftWordReconstruct, rightWordReconstruct] using ownerValid
            have prefixValid :=
              ownerStripUniqueFinal leftFinal leftWord rightWord
                leftAbsentWord rightAbsentWord whole
            have prefixDerivation :=
              SemigroupBasis.CoRoots.S5_1149.representative_basis.2
                (Identity.mk leftWord rightWord) prefixValid
            have lifted :=
              liftS5_1149UnderFinalGuard prefixDerivation
                (Word.singleton leftFinal) Word.singleton
            rw [bind_singleton, bind_singleton] at lifted
            simpa [leftWordReconstruct, rightWordReconstruct] using lifted
  · have leftRepeated : leftFinal ∈ leftPrefix :=
      Decidable.byContradiction leftSimple
    have rightRepeated : rightFinal ∈ rightPrefix := by
      apply Decidable.byContradiction
      intro rightAbsent
      have transported :=
        (finalMarkerValid_splitSimpleFinal_iff
          identity markerValid rightFinal).mpr ⟨rfl, rightAbsent⟩
      have finals : leftFinal = rightFinal := transported.1
      exact transported.2 (by simpa [finals] using leftRepeated)
    have heads := leftValid_head identity leftValid
    let guard : Word Nat :=
      (Word.singleton identity.lhs.head ++
        Word.singleton identity.lhs.head) ++
          Word.singleton identity.lhs.head
    have leftExpanded : Derives basis identity.lhs
        (identity.lhs ++ guard) := by
      simpa [guard, leftPrefix, leftFinal] using
        derivesAppendInitialTriple_of_repeatedFinal
          identity.lhs leftRepeated
    have rightExpanded : Derives basis identity.rhs
        (identity.rhs ++ guard) := by
      simpa [guard, heads, rightPrefix, rightFinal] using
        derivesAppendInitialTriple_of_repeatedFinal
          identity.rhs rightRepeated
    have lifted :=
      liftS5_1149UnderFinalGuard lower guard Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    exact leftExpanded.trans (lifted.trans rightExpanded.symm)

/-- Package the pair only after its unrestricted completeness proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derives_of_factor_valid

/-- Certified reusable rank-069 family seed. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Unconditional direct orientation for the authenticated class. -/
theorem s6_14910_representative_basis :
    BasisFor S6_14910.table.semigroup basis :=
  S6_14910.representative_basis_of_normalizer normalizer

/-- Unconditional opposite orientation for the authenticated class. -/
theorem s6_14910_opposite_basis :
    BasisFor S6_14910.table.semigroup.opposite (reversedBasis basis) :=
  S6_14910.opposite_basis_of_normalizer normalizer

/-- Reviewed generic transport keeps all three independent proof premises. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank069.Seed

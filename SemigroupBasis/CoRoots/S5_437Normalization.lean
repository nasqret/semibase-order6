import SemigroupBasis.CoRoots.S4_90
import SemigroupBasis.CoRoots.S5_437
import SemigroupBasis.Examples.FinalMarkerThree

namespace SemigroupBasis.CoRoots.S5_437

open SemigroupBasis
open SemigroupBasis.Examples

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (τ σ : Nat → Word Nat) :
    (word.bind τ).bind σ =
      word.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem suffixParity_finiteBasis_checked :
    finiteBasis.all
      Generated.Catalogue.S4_90.table.checkIdentity = true := by
  decide

/-- The suffix-parity factor models every law of the 23-law basis. -/
theorem basis_models_suffixParity :
    Models Generated.Catalogue.S4_90.table.semigroup basis :=
  models_of_finite_checks
    Generated.Catalogue.S4_90.table
    suffixParity_finiteBasis_checked

/-- Replay a derivation for the `S4_90` suffix-parity basis while retaining
a fixed nonempty suffix. The target laws realize `x = x³` and
`xyz = xzy` only when that suffix is present. -/
theorem liftSuffixParity
    {u v : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S4_90.basis u v)
    (rightContext : Word Nat) (σ : Nat → Word Nat) :
    Derives basis
      (u.bind σ ++ rightContext)
      (v.bind σ ++ rightContext) := by
  induction derivation generalizing rightContext σ with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S4_90.basis,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [
          SemigroupBasis.CoRoots.S4_90.suffixParityCommutationLaw,
          SemigroupBasis.CoRoots.S4_90.suffixParityXYZ,
          SemigroupBasis.CoRoots.S4_90.suffixParityXZY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesInteriorSwap
            (σ 0) (σ 1) (σ 2) rightContext
      · simpa [
          SemigroupBasis.CoRoots.S4_90.suffixParityPowerLaw,
          SemigroupBasis.CoRoots.S4_90.suffixParityX,
          SemigroupBasis.CoRoots.S4_90.suffixParityXXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesPrefixPairExpansion (σ 0) rightContext
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih rightContext σ)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans
        (ih₁ rightContext σ) (ih₂ rightContext σ)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (p.bind σ) (ih rightContext σ)
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        ih (q.bind σ ++ rightContext) σ
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih rightContext (fun x => (τ x).bind σ)

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem wordOfCons_append_singleton
    (head : Nat) (tail : List Nat) (final : Nat) :
    wordOfCons head tail ++ Word.singleton final =
      wordOfPrefixFinal (head :: tail) final := by
  apply Word.toList_injective
  rw [Word.toList_append, Word.toList_singleton,
    toList_wordOfPrefixFinal]
  rfl

private theorem wordOfCons_append_wordOfPrefixFinal
    (head : Nat) (tail middle : List Nat) (final : Nat) :
    wordOfCons head tail ++ wordOfPrefixFinal middle final =
      wordOfPrefixFinal (head :: (tail ++ middle)) final := by
  apply Word.toList_injective
  rw [Word.toList_append, toList_wordOfPrefixFinal,
    toList_wordOfPrefixFinal]
  simp only [wordOfCons, Word.toList, List.cons_append,
    List.append_assoc]

/-- The `S4_90` basis derives any identity whose two words have the same
first letter, support, and coordinate parity. -/
theorem suffixParityDerivesOfInvariants
    (u v : Word Nat)
    (heads : u.head = v.head)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity : ∀ z, u.toList.count z % 2 =
      v.toList.count z % 2) :
    Derives SemigroupBasis.CoRoots.S4_90.basis u v := by
  have lhsNormal :=
    SemigroupBasis.CoRoots.S4_90.derivesNormal u
  have rhsNormal :=
    SemigroupBasis.CoRoots.S4_90.derivesNormal v
  have middle :
      Derives SemigroupBasis.CoRoots.S4_90.basis
        (SemigroupBasis.CoRoots.S4_90.normal u)
        (SemigroupBasis.CoRoots.S4_90.normal v) := by
    simpa [SemigroupBasis.CoRoots.S4_90.normal,
      wordOfCons, heads] using
      SemigroupBasis.CoRoots.S4_90.derivesTailPermutation
        u.head
        (SemigroupBasis.CoRoots.S4_90.normal_tail_perm
          u v heads support parity)
  exact Derives.trans lhsNormal <|
    Derives.trans middle (Derives.symm rhsNormal)

/-- Replay a suffix-parity derivation while retaining one common final
letter. -/
theorem derivesSuffixParityUnderFinal
    (u v : Word Nat) (final : Nat)
    (heads : u.head = v.head)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parity : ∀ z, u.toList.count z % 2 =
      v.toList.count z % 2) :
    Derives basis
      (u ++ Word.singleton final)
      (v ++ Word.singleton final) := by
  have lifted :=
    liftSuffixParity
      (suffixParityDerivesOfInvariants
        u v heads support parity)
      (Word.singleton final) Word.singleton
  simpa [bind_singleton] using lifted

/-- Permute a prefix tail while retaining both its first letter and a common
final letter. -/
theorem derivesTailPermutationUnderFinal
    (head final : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    Derives basis
      (wordOfCons head left ++ Word.singleton final)
      (wordOfCons head right ++ Word.singleton final) := by
  have lifted :=
    liftSuffixParity
      (SemigroupBasis.CoRoots.S4_90.derivesTailPermutation
        head permutation)
      (Word.singleton final) Word.singleton
  simpa [bind_singleton] using lifted

/-- Tail of the prefix obtained after changing a repeated final letter to
the fixed first letter. -/
def headAlignedTail
    (head : Nat) (tail : List Nat) (final : Nat) : List Nat :=
  if final = head then
    tail
  else
    tail.erase final ++ [head, final, final]

private theorem expandedTail_perm_headAligned
    (head final : Nat) (tail : List Nat)
    (different : final ≠ head)
    (repeated : final ∈ tail) :
    (head :: head :: tail).Perm
      (tail.erase final ++ [head, head, final]) := by
  rw [List.perm_iff_count]
  intro z
  simp only [List.count_append]
  by_cases hz : z = final
  · subst z
    rw [List.count_erase_self]
    have positive : 0 < tail.count final :=
      List.count_pos_iff.mpr repeated
    simp [Ne.symm different]
    omega
  · rw [List.count_erase_of_ne hz]
    by_cases zh : z = head
    · subst z
      simp [different]
    · simp [Ne.symm hz, Ne.symm zh]

/-- If the final letter is globally repeated, change it to the first letter.
Only parity-neutral pairs are introduced, and the old final occurrence is
retained twice inside the new prefix. -/
theorem derivesRepeatedFinalToHead
    (head : Nat) (tail : List Nat) (final : Nat)
    (repeated : final ∈ head :: tail) :
    Derives basis
      (wordOfPrefixFinal (head :: tail) final)
      (wordOfPrefixFinal
        (head :: headAlignedTail head tail final) head) := by
  by_cases different : final ≠ head
  · have finalInTail : final ∈ tail := by
      simpa [different] using repeated
    have expandedRaw :=
      derivesPrefixPairExpansion
        (Word.singleton head)
        (wordOfPrefixFinal tail final)
    have expanded :
        Derives basis
          (wordOfPrefixFinal (head :: tail) final)
          (wordOfCons head (head :: head :: tail) ++
            Word.singleton final) := by
      rw [wordOfCons_append_singleton]
      simpa only [wordOfPrefixFinal_cons, Word.append_assoc] using
        expandedRaw
    have arranged :=
      derivesTailPermutationUnderFinal head final
        (expandedTail_perm_headAligned
          head final tail different finalInTail)
    have switchedPattern :
        Derives basis
          (wordOfPrefixFinal [head, head, final] final)
          (wordOfPrefixFinal [head, final, final] head) := by
      simpa [wordOfPrefixFinal, Word.append_assoc] using
        derivesFinalSwitchPattern
          (Word.singleton head) (Word.singleton final)
    have switchedRaw :=
      Derives.prepend
        (wordOfCons head (tail.erase final))
        switchedPattern
    have switched :
        Derives basis
          (wordOfCons head
              (tail.erase final ++ [head, head, final]) ++
            Word.singleton final)
          (wordOfPrefixFinal
            (head ::
              (tail.erase final ++ [head, final, final])) head) := by
      rw [wordOfCons_append_singleton]
      simpa only [wordOfCons_append_wordOfPrefixFinal] using
        switchedRaw
    simpa [headAlignedTail, different] using
      expanded.trans (arranged.trans switched)
  · have equal : final = head := by
      exact Decidable.not_not.mp different
    subst final
    simpa [headAlignedTail] using
      (Derives.refl
        (wordOfPrefixFinal (head :: tail) head) :
        Derives basis
          (wordOfPrefixFinal (head :: tail) head)
          (wordOfPrefixFinal (head :: tail) head))

/-- Remove a common final occurrence from support equality, provided that
the final letter occurs in both prefixes or in neither prefix. -/
private theorem prefixSupport_of_commonFinal
    (head : Nat) (left right : List Nat) (final : Nat)
    (finalMembership :
      final ∈ head :: left ↔ final ∈ head :: right)
    (support :
      ∀ z,
        z ∈
            (wordOfPrefixFinal (head :: left) final).toList ↔
          z ∈
            (wordOfPrefixFinal (head :: right) final).toList) :
    ∀ z,
      z ∈ (wordOfCons head left).toList ↔
        z ∈ (wordOfCons head right).toList := by
  intro z
  by_cases equal : z = final
  · subst z
    simpa [wordOfCons, Word.toList] using finalMembership
  · have whole := support z
    rw [toList_wordOfPrefixFinal,
      toList_wordOfPrefixFinal] at whole
    change z ∈ head :: left ↔ z ∈ head :: right
    simpa [equal] using whole

/-- Remove a common final occurrence from coordinate-parity equality. -/
private theorem prefixParity_of_commonFinal
    (head : Nat) (left right : List Nat) (final : Nat)
    (parity :
      ∀ z,
        (wordOfPrefixFinal
            (head :: left) final).toList.count z % 2 =
          (wordOfPrefixFinal
            (head :: right) final).toList.count z % 2) :
    ∀ z,
      (wordOfCons head left).toList.count z % 2 =
        (wordOfCons head right).toList.count z % 2 := by
  intro z
  have whole := parity z
  rw [toList_wordOfPrefixFinal,
    toList_wordOfPrefixFinal] at whole
  change
    (head :: left).count z % 2 =
      (head :: right).count z % 2
  by_cases equal : z = final
  · subst z
    simp only [List.count_append, List.count_cons_self,
      List.count_nil, Nat.zero_add] at whole
    omega
  · have singletonCount : [final].count z = 0 :=
      List.count_eq_zero.mpr <| by
        simpa using equal
    simp only [List.count_append] at whole
    simpa [singletonCount] using whole

/-- Words with a common first and final letter are derivably equal once
their full supports and parity vectors agree and the final letter has the
same prefix-membership status on both sides. -/
theorem derivesCommonFinalOfInvariants
    (head : Nat) (left right : List Nat) (final : Nat)
    (finalMembership :
      final ∈ head :: left ↔ final ∈ head :: right)
    (support :
      ∀ z,
        z ∈
            (wordOfPrefixFinal (head :: left) final).toList ↔
          z ∈
            (wordOfPrefixFinal (head :: right) final).toList)
    (parity :
      ∀ z,
        (wordOfPrefixFinal
            (head :: left) final).toList.count z % 2 =
          (wordOfPrefixFinal
            (head :: right) final).toList.count z % 2) :
    Derives basis
      (wordOfPrefixFinal (head :: left) final)
      (wordOfPrefixFinal (head :: right) final) := by
  have derivation :=
    derivesSuffixParityUnderFinal
      (wordOfCons head left) (wordOfCons head right) final
      rfl
      (prefixSupport_of_commonFinal
        head left right final finalMembership support)
      (prefixParity_of_commonFinal
        head left right final parity)
  simpa only [wordOfCons_append_singleton] using derivation

/-- Complete syntactic normalization for two explicit non-singleton words.
The hypotheses are exactly support, parity, first letter, and globally
simple final letter. In the repeated-final branch both words are first
changed to end in their common first letter. -/
theorem derivesOfParityFirstFinalInvariants
    (head : Nat) (left right : List Nat)
    (leftFinal rightFinal : Nat)
    (support :
      ∀ z,
        z ∈
            (wordOfPrefixFinal
              (head :: left) leftFinal).toList ↔
          z ∈
            (wordOfPrefixFinal
              (head :: right) rightFinal).toList)
    (parity :
      ∀ z,
        (wordOfPrefixFinal
            (head :: left) leftFinal).toList.count z % 2 =
          (wordOfPrefixFinal
            (head :: right) rightFinal).toList.count z % 2)
    (simpleFinal :
      ∀ z,
        (leftFinal = z ∧ z ∉ head :: left) ↔
          (rightFinal = z ∧ z ∉ head :: right)) :
    Derives basis
      (wordOfPrefixFinal (head :: left) leftFinal)
      (wordOfPrefixFinal (head :: right) rightFinal) := by
  by_cases leftSimple : leftFinal ∉ head :: left
  · have rightSimple :=
      (simpleFinal leftFinal).mp ⟨rfl, leftSimple⟩
    rcases rightSimple with ⟨rightFinalEq, rightAbsent⟩
    subst rightFinal
    exact derivesCommonFinalOfInvariants
      head left right leftFinal
      (iff_of_false leftSimple rightAbsent)
      support parity
  · have leftRepeated : leftFinal ∈ head :: left := by
      exact Decidable.not_not.mp leftSimple
    have rightRepeated : rightFinal ∈ head :: right := by
      apply Decidable.byContradiction
      intro rightAbsent
      have leftMarker :=
        (simpleFinal rightFinal).mpr ⟨rfl, rightAbsent⟩
      rcases leftMarker with ⟨finalsEq, leftAbsent⟩
      subst rightFinal
      exact leftAbsent leftRepeated
    let leftTail := headAlignedTail head left leftFinal
    let rightTail := headAlignedTail head right rightFinal
    have alignLeft :
        Derives basis
          (wordOfPrefixFinal (head :: left) leftFinal)
          (wordOfPrefixFinal (head :: leftTail) head) := by
      simpa [leftTail] using
        derivesRepeatedFinalToHead
          head left leftFinal leftRepeated
    have alignRight :
        Derives basis
          (wordOfPrefixFinal (head :: right) rightFinal)
          (wordOfPrefixFinal (head :: rightTail) head) := by
      simpa [rightTail] using
        derivesRepeatedFinalToHead
          head right rightFinal rightRepeated
    have originalSuffixDerivation :
        Derives SemigroupBasis.CoRoots.S4_90.basis
          (wordOfPrefixFinal (head :: left) leftFinal)
          (wordOfPrefixFinal (head :: right) rightFinal) :=
      suffixParityDerivesOfInvariants
        (wordOfPrefixFinal (head :: left) leftFinal)
        (wordOfPrefixFinal (head :: right) rightFinal)
        rfl support parity
    let alignedIdentity : Identity Nat :=
      ⟨wordOfPrefixFinal (head :: leftTail) head,
        wordOfPrefixFinal (head :: rightTail) head⟩
    have alignedValid :
        alignedIdentity.SatisfiedBy
          Generated.Catalogue.S4_90.table.semigroup := by
      intro valuation
      have leftSound :=
        alignLeft.sound basis_models_suffixParity valuation
      have originalSound :=
        originalSuffixDerivation.sound
          SemigroupBasis.CoRoots.S4_90.models valuation
      have rightSound :=
        alignRight.sound basis_models_suffixParity valuation
      exact leftSound.symm.trans <|
        originalSound.trans rightSound
    have alignedSupport :
        ∀ z,
          z ∈
              (wordOfPrefixFinal
                (head :: leftTail) head).toList ↔
            z ∈
              (wordOfPrefixFinal
                (head :: rightTail) head).toList := by
      exact
        SemigroupBasis.CoRoots.S4_90.valid_support
          alignedIdentity alignedValid
    have alignedParity :
        ∀ z,
          (wordOfPrefixFinal
              (head :: leftTail) head).toList.count z % 2 =
            (wordOfPrefixFinal
              (head :: rightTail) head).toList.count z % 2 := by
      exact
        SemigroupBasis.CoRoots.S4_90.valid_parity
          alignedIdentity alignedValid
    have middle :
        Derives basis
          (wordOfPrefixFinal (head :: leftTail) head)
          (wordOfPrefixFinal (head :: rightTail) head) :=
      derivesCommonFinalOfInvariants
        head leftTail rightTail head
        (by simp) alignedSupport alignedParity
    exact alignLeft.trans <|
      middle.trans alignRight.symm

/-- Generic completeness theorem for any semigroup whose valid identities
preserve support, coordinate parity, the first letter, and the globally
simple final letter. -/
theorem basis_complete_of_parity_first_final
    (G : Semigroup S)
    (modelsG : Models G basis)
    (headsG :
      ∀ e : Identity Nat, e.SatisfiedBy G →
        e.lhs.head = e.rhs.head)
    (supportG :
      ∀ e : Identity Nat, e.SatisfiedBy G →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (parityG :
      ∀ e : Identity Nat, e.SatisfiedBy G →
        ∀ z, e.lhs.toList.count z % 2 =
          e.rhs.toList.count z % 2)
    (simpleFinalG :
      ∀ e : Identity Nat, e.SatisfiedBy G →
        ∀ z,
          ((splitPrefixFinal e.lhs).2 = z ∧
              z ∉ (splitPrefixFinal e.lhs).1) ↔
            ((splitPrefixFinal e.rhs).2 = z ∧
              z ∉ (splitPrefixFinal e.rhs).1)) :
    BasisFor G basis := by
  refine ⟨modelsG, ?_⟩
  intro e valid
  let lhsSplit := splitPrefixFinal e.lhs
  let rhsSplit := splitPrefixFinal e.rhs
  have lhsReconstruct :
      wordOfPrefixFinal lhsSplit.1 lhsSplit.2 = e.lhs :=
    wordOfPrefixFinal_split e.lhs
  have rhsReconstruct :
      wordOfPrefixFinal rhsSplit.1 rhsSplit.2 = e.rhs :=
    wordOfPrefixFinal_split e.rhs
  have heads := headsG e valid
  have support := supportG e valid
  have parity := parityG e valid
  have simpleFinal := simpleFinalG e valid
  change
    ∀ z,
      (lhsSplit.2 = z ∧ z ∉ lhsSplit.1) ↔
        (rhsSplit.2 = z ∧ z ∉ rhsSplit.1)
    at simpleFinal
  rw [← lhsReconstruct, ← rhsReconstruct] at heads support parity
  cases lhsShape : lhsSplit.1 with
  | nil =>
      cases rhsShape : rhsSplit.1 with
      | nil =>
          have rightMarker :=
            (simpleFinal lhsSplit.2).mp <| by
              simp [lhsShape]
          have finals : rhsSplit.2 = lhsSplit.2 :=
            rightMarker.1
          have wordsEqual : e.lhs = e.rhs := by
            rw [← lhsReconstruct, ← rhsReconstruct,
              lhsShape, rhsShape, finals]
          rw [wordsEqual]
          exact Derives.refl _
      | cons rhsHead rhsTail =>
          have rightMarker :=
            (simpleFinal lhsSplit.2).mp <| by
              simp [lhsShape]
          have prefixHead :
              lhsSplit.2 = rhsHead := by
            simpa [lhsShape, rhsShape, wordOfPrefixFinal] using heads
          have forbidden :
              lhsSplit.2 ∈ rhsHead :: rhsTail := by
            simp [prefixHead]
          exact False.elim <| rightMarker.2 <| by
            simpa [rhsShape] using forbidden
  | cons lhsHead lhsTail =>
      cases rhsShape : rhsSplit.1 with
      | nil =>
          have leftMarker :=
            (simpleFinal rhsSplit.2).mpr <| by
              simp [rhsShape]
          have prefixHead :
              lhsHead = rhsSplit.2 := by
            simpa [lhsShape, rhsShape, wordOfPrefixFinal] using heads
          have forbidden :
              rhsSplit.2 ∈ lhsHead :: lhsTail := by
            simp [prefixHead]
          exact False.elim <| leftMarker.2 <| by
            simpa [lhsShape] using forbidden
      | cons rhsHead rhsTail =>
          have prefixHeads : lhsHead = rhsHead := by
            simpa [lhsShape, rhsShape, wordOfPrefixFinal] using heads
          subst rhsHead
          have explicitSupport :
              ∀ z,
                z ∈
                    (wordOfPrefixFinal
                      (lhsHead :: lhsTail) lhsSplit.2).toList ↔
                  z ∈
                    (wordOfPrefixFinal
                      (lhsHead :: rhsTail) rhsSplit.2).toList := by
            intro z
            simpa [lhsShape, rhsShape] using support z
          have explicitParity :
              ∀ z,
                (wordOfPrefixFinal
                    (lhsHead :: lhsTail)
                    lhsSplit.2).toList.count z % 2 =
                  (wordOfPrefixFinal
                    (lhsHead :: rhsTail)
                    rhsSplit.2).toList.count z % 2 := by
            intro z
            simpa [lhsShape, rhsShape] using parity z
          have explicitSimpleFinal :
              ∀ z,
                (lhsSplit.2 = z ∧
                    z ∉ lhsHead :: lhsTail) ↔
                  (rhsSplit.2 = z ∧
                    z ∉ lhsHead :: rhsTail) := by
            intro z
            simpa [lhsShape, rhsShape] using simpleFinal z
          have explicit :=
            derivesOfParityFirstFinalInvariants
              lhsHead lhsTail rhsTail lhsSplit.2 rhsSplit.2
              explicitSupport explicitParity explicitSimpleFinal
          rw [lhsShape] at lhsReconstruct
          rw [rhsShape] at rhsReconstruct
          rw [← lhsReconstruct, ← rhsReconstruct]
          exact explicit

end SemigroupBasis.CoRoots.S5_437

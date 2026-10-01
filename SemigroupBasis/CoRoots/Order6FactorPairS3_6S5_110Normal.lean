import SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110Prelude
import SemigroupBasis.CoRoots.Order6FinalMarkerM2

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110

open SemigroupBasis
open SemigroupBasis.Examples

private def xx : Word Nat := Word.mk 0 [0]
private def xxx : Word Nat := Word.mk 0 [0, 0]
private def xxyy : Word Nat := Word.mk 0 [0, 1, 1]
private def xyyx : Word Nat := Word.mk 0 [1, 1, 0]
private def xxyz : Word Nat := Word.mk 0 [0, 1, 2]
private def xyxz : Word Nat := Word.mk 0 [1, 0, 2]
private def xyx : Word Nat := Word.mk 0 [1, 0]
private def yxx : Word Nat := Word.mk 1 [0, 0]

private theorem basisPower : Derives basis xx xxx :=
  Derives.fromBasis (e := Identity.mk xx xxx) (by decide)

private theorem basisRepeatedFinal : Derives basis xxyy xyyx :=
  Derives.fromBasis (e := Identity.mk xxyy xyyx) (by decide)

private theorem basisDoubledInitialMove : Derives basis xxyz xyxz :=
  Derives.fromBasis (e := Identity.mk xxyz xyxz) (by decide)

private theorem basisRightGather : Derives basis xyx yxx :=
  Derives.fromBasis (e := Identity.mk xyx yxx) (by decide)

private def instantiateThreeWords
    (u v suffix : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => suffix
  | n + 3 => Word.singleton (n + 3)

private theorem bind_append
    (left right : Word Nat) (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- Substitute a nonempty block into the imported target power law. -/
theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [xx, xxx, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesPowerContraction (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) :=
  (derivesPowerExpansion u).symm

/-- The common repeated-final switch, obtained from the second imported
candidate law. -/
theorem derivesRepeatedFinalSwitch (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisRepeatedFinal
      (instantiateThreeWords u v v)
  simpa [xxyy, xyyx, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Move one copy of a doubled initial block across a protected nonempty
suffix. -/
theorem derivesDoubledInitialMove
    (u v suffix : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ suffix)
      (((u ++ v) ++ u) ++ suffix) := by
  have substituted :=
    Derives.subst basisDoubledInitialMove
      (instantiateThreeWords u v suffix)
  simpa [xxyz, xyxz, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

theorem derivesRightGather (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) ((v ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisRightGather
      (instantiateThreeWords u v v)
  simpa [xyx, yxx, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Every law of the cap-three M2 presentation follows from the target
presentation. Its sole different law, `xxx = xxxx`, is the target power
law with one copy appended. -/
private theorem m2AxiomDerives
    (identity : Identity Nat)
    (member :
      identity ∈ Order6FinalMarkerM2.basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [Order6FinalMarkerM2.basis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · have appended :=
      Derives.appendRight
        (derivesPowerExpansion (Word.singleton 0))
        (Word.singleton 0)
    simpa [Order6FinalMarkerM2.powerLaw,
      Order6FinalMarkerM2.xxx, Order6FinalMarkerM2.xxxx,
      Word.singleton, Word.append, Word.append_assoc] using appended
  · simpa [Order6FinalMarkerM2.repeatedFinalLaw,
      Order6FinalMarkerM2.xxyy, Order6FinalMarkerM2.xyyx,
      Word.singleton, Word.append, Word.append_assoc] using
        derivesRepeatedFinalSwitch
          (Word.singleton 0) (Word.singleton 1)
  · simpa [Order6FinalMarkerM2.doubledInitialMoveLaw,
      Order6FinalMarkerM2.xxyz, Order6FinalMarkerM2.xyxz,
      Word.singleton, Word.append, Word.append_assoc] using
        derivesDoubledInitialMove
          (Word.singleton 0) (Word.singleton 1) (Word.singleton 2)
  · simpa [Order6FinalMarkerM2.rightGatherLaw,
      Order6FinalMarkerM2.xyx, Order6FinalMarkerM2.yxx,
      Word.singleton, Word.append, Word.append_assoc] using
        derivesRightGather (Word.singleton 0) (Word.singleton 1)

private theorem s5_110_xx_eq :
    S5_110.xx = (⟨0, [0]⟩ : Word Nat) :=
  rfl

private theorem s5_110_xxx_eq :
    S5_110.xxx = (⟨0, [0, 0]⟩ : Word Nat) :=
  rfl

private theorem s5_110_xyx_eq :
    S5_110.xyx = (⟨0, [1, 0]⟩ : Word Nat) :=
  rfl

private theorem s5_110_xxy_eq :
    S5_110.xxy = (⟨0, [0, 1]⟩ : Word Nat) :=
  rfl

private theorem s5_110_yxx_eq :
    S5_110.yxx = (⟨1, [0, 0]⟩ : Word Nat) :=
  rfl

/-- Replay an arbitrary S5_110 derivation while retaining a protected
nonempty suffix. The unprotected left-gather step is supplied by
`xxyz = xyxz` in the reverse direction. -/
theorem liftS5_110Derivation
    {left right : Word Nat}
    (derivation : Derives S5_110.basis left right)
    (suffix : Word Nat) (substitution : Nat → Word Nat) :
    Derives basis
      (left.bind substitution ++ suffix)
      (right.bind substitution ++ suffix) := by
  induction derivation generalizing suffix substitution with
  | fromBasis member =>
      simp only [S5_110.basis, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [S5_110.powerLaw, s5_110_xx_eq, s5_110_xxx_eq,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.appendRight
              (derivesPowerExpansion (substitution 0)) suffix
      · simpa [S5_110.leftFoldLaw, s5_110_xyx_eq, s5_110_xxy_eq,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            (derivesDoubledInitialMove
              (substitution 0) (substitution 1) suffix).symm
      · simpa [S5_110.rightFoldLaw, s5_110_xyx_eq, s5_110_yxx_eq,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.appendRight
              (derivesRightGather
                (substitution 0) (substitution 1)) suffix
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction suffix substitution)
  | trans _ _ first second =>
      exact (first suffix substitution).trans
        (second suffix substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution)
          (induction suffix substitution)
  | appendRight _ appended induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (appended.bind substitution ++ suffix) substitution
  | subst _ firstSubstitution induction =>
      simpa [bind_bind] using
        induction suffix
          (fun letter =>
            (firstSubstitution letter).bind substitution)

theorem liftS5_110DerivationWithSuffix
    {left right : Word Nat}
    (derivation : Derives S5_110.basis left right)
    (suffix : Word Nat) :
    Derives basis (left ++ suffix) (right ++ suffix) := by
  simpa [bind_singleton] using
    liftS5_110Derivation derivation suffix Word.singleton

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem markerModels :
    Models Generated.S3_6.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    Generated.S3_6.table basis toFinThree (by decide)

theorem s5Models :
    Models Generated.Catalogue.S5_110.table.semigroup basis :=
  FiniteCertificate.checkModels_sound
    Generated.Catalogue.S5_110.table basis toFinThree (by decide)

private theorem count_renderRepeatedBlocks
    (letters : List Nat) (tested : Nat) :
    (letters.flatMap S5_110Syntax.renderRepeatedBlock).count tested =
      2 * letters.count tested := by
  induction letters with
  | nil =>
      simp
  | cons head tail induction =>
      rw [List.flatMap_cons, List.count_append, induction]
      by_cases same : head = tested
      · subst head
        simp [S5_110Syntax.renderRepeatedBlock]
        omega
      · simp [S5_110Syntax.renderRepeatedBlock, same]

/-- The public S5_110 canonical word is genuinely two-limited, not merely
equivalent modulo cap two. -/
private theorem canonicalWord_count_le_two
    (word : Word Nat) (tested : Nat) :
    (S5_110Syntax.canonicalWord word).toList.count tested ≤ 2 := by
  rw [S5_110Syntax.toList_canonicalWord,
    S5_110Syntax.canonicalList, List.count_append,
    count_renderRepeatedBlocks,
    (S5_110Syntax.singletonSequence_nodup word).count,
    (S5_110Syntax.sortedRepeatedLetters_nodup word).count]
  by_cases simple : word.toList.count tested = 1
  · have singletonMember :
        tested ∈ S5_110Syntax.singletonSequence word :=
      (S5_110Syntax.mem_singletonSequence_iff word tested).2 simple
    have repeatedAbsent :
        tested ∉ S5_110Syntax.sortedRepeatedLetters word := by
      intro repeated
      have multiple :=
        (S5_110Syntax.mem_sortedRepeatedLetters_iff word tested).1
          repeated
      omega
    simp [singletonMember, repeatedAbsent]
  · have singletonAbsent :
        tested ∉ S5_110Syntax.singletonSequence word := by
      intro singleton
      exact simple <|
        (S5_110Syntax.mem_singletonSequence_iff word tested).1
          singleton
    by_cases repeated :
        tested ∈ S5_110Syntax.sortedRepeatedLetters word
    · simp [singletonAbsent, repeated]
    · simp [singletonAbsent, repeated]

private def finalCopies (stem : List Nat) (final : Nat) : Nat :=
  Nat.min 2 (stem.count final + 1)

private theorem finalCopies_positive (stem : List Nat) (final : Nat) :
    0 < finalCopies stem final := by
  unfold finalCopies
  simp only [Nat.min_def]
  split <;> omega

private theorem finalCopies_le_two (stem : List Nat) (final : Nat) :
    finalCopies stem final ≤ 2 :=
  Nat.min_le_left _ _

private theorem replicate_sub_one_append_singleton
    (letter copies : Nat) (positive : 0 < copies) :
    List.replicate (copies - 1) letter ++ [letter] =
      List.replicate copies letter := by
  cases copies with
  | zero => omega
  | succ copies =>
      induction copies with
      | zero => simp
      | succ copies induction =>
          simpa [List.replicate_succ, List.cons_append] using
            congrArg (List.cons letter) (induction (by omega))

private def finalNormalList
    (stem : List Nat) (final : Nat) : List Nat :=
  Order6FinalMarkerM2.removeLetter final stem ++
    List.replicate (finalCopies stem final) final

private def finalNormalWord
    (stem : List Nat) (final : Nat) : Word Nat :=
  wordOfPrefixFinal
    (Order6FinalMarkerM2.removeLetter final stem ++
      List.replicate (finalCopies stem final - 1) final)
    final

private theorem toList_finalNormalWord
    (stem : List Nat) (final : Nat) :
    (finalNormalWord stem final).toList =
      finalNormalList stem final := by
  unfold finalNormalWord finalNormalList
  rw [toList_wordOfPrefixFinal, List.append_assoc,
    replicate_sub_one_append_singleton final
      (finalCopies stem final)
      (finalCopies_positive stem final)]

private def finalBlockWord (final copies : Nat) : Word Nat :=
  Word.mk final (List.replicate (copies - 1) final)

private theorem toList_finalBlockWord
    (final copies : Nat) (positive : 0 < copies) :
    (finalBlockWord final copies).toList =
      List.replicate copies final := by
  cases copies with
  | zero => omega
  | succ copies =>
      simp [finalBlockWord, Word.toList, List.replicate_succ]

private theorem count_replicate_of_ne
    {value tested : Nat} (different : tested ≠ value) :
    ∀ copies : Nat, (List.replicate copies value).count tested = 0
  | 0 => rfl
  | copies + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different copies]

private theorem finalBlock_count_le_two
    (final copies tested : Nat)
    (positive : 0 < copies) (upper : copies ≤ 2) :
    (finalBlockWord final copies).toList.count tested ≤ 2 := by
  rw [toList_finalBlockWord final copies positive]
  by_cases same : tested = final
  · subst tested
    simpa using upper
  · calc
      (List.replicate copies final).count tested = 0 :=
        count_replicate_of_ne same copies
      _ ≤ 2 := by omega

private theorem finalNormalWord_eq_block
    (stem : List Nat) (final copies : Nat)
    (copiesEq : finalCopies stem final = copies)
    (bodyEmpty :
      Order6FinalMarkerM2.removeLetter final stem = []) :
    finalNormalWord stem final = finalBlockWord final copies := by
  apply Word.toList_injective
  rw [toList_finalNormalWord,
    toList_finalBlockWord final copies (by
      rw [← copiesEq]
      exact finalCopies_positive stem final)]
  simp [finalNormalList, bodyEmpty, copiesEq]

private theorem finalNormalWord_eq_body_append
    (stem : List Nat) (final copies : Nat)
    (copiesEq : finalCopies stem final = copies)
    {head : Nat} {tail : List Nat}
    (bodyShape :
      Order6FinalMarkerM2.removeLetter final stem = head :: tail) :
    finalNormalWord stem final =
      S5_107.listWordOfCons head tail ++
        finalBlockWord final copies := by
  apply Word.toList_injective
  rw [toList_finalNormalWord, Word.toList_append,
    toList_finalBlockWord final copies (by
      rw [← copiesEq]
      exact finalCopies_positive stem final)]
  simp [finalNormalList, bodyShape, copiesEq,
    S5_107.listWordOfCons, Word.toList]

private theorem m2FinalNormalWord_eq_block
    (stem : List Nat) (final copies : Nat)
    (copiesEq : Order6FinalMarkerM2.finalCopies stem final = copies)
    (bodyEmpty :
      Order6FinalMarkerM2.removeLetter final stem = []) :
    Order6FinalMarkerM2.finalNormalWord stem final =
      finalBlockWord final copies := by
  apply Word.toList_injective
  rw [Order6FinalMarkerM2.toList_finalNormalWord,
    toList_finalBlockWord final copies (by
      rw [← copiesEq]
      exact Order6FinalMarkerM2.finalCopies_positive stem final)]
  simp [Order6FinalMarkerM2.finalNormalList, bodyEmpty, copiesEq]

private theorem m2FinalNormalWord_eq_body_append
    (stem : List Nat) (final copies : Nat)
    (copiesEq : Order6FinalMarkerM2.finalCopies stem final = copies)
    {head : Nat} {tail : List Nat}
    (bodyShape :
      Order6FinalMarkerM2.removeLetter final stem = head :: tail) :
    Order6FinalMarkerM2.finalNormalWord stem final =
      S5_107.listWordOfCons head tail ++
        finalBlockWord final copies := by
  apply Word.toList_injective
  rw [Order6FinalMarkerM2.toList_finalNormalWord,
    Word.toList_append,
    toList_finalBlockWord final copies (by
      rw [← copiesEq]
      exact Order6FinalMarkerM2.finalCopies_positive stem final)]
  simp [Order6FinalMarkerM2.finalNormalList, bodyShape, copiesEq,
    S5_107.listWordOfCons, Word.toList]

private theorem derivesBlockThreeToTwo (final : Nat) :
    Derives basis (finalBlockWord final 3)
      (finalBlockWord final 2) := by
  simpa [finalBlockWord, Word.singleton, Word.append,
    Word.append_assoc, List.replicate_succ] using
      derivesPowerContraction (Word.singleton final)

/-- Reuse the cap-three M2 gatherer and contract its only extra terminal
copy. This is the complete specialization of the M2 final normalization
stage from cap three to cap two. -/
private theorem derivesFinalNormal (stem : List Nat) (final : Nat) :
    Derives basis
      (wordOfPrefixFinal stem final)
      (finalNormalWord stem final) := by
  have m2Normal :=
    (Order6FinalMarkerM2.derivesFinalNormal stem final).transport
      m2AxiomDerives
  by_cases small : stem.count final + 1 ≤ 2
  · have m2Copies :
        Order6FinalMarkerM2.finalCopies stem final =
          stem.count final + 1 := by
      unfold Order6FinalMarkerM2.finalCopies
      exact Nat.min_eq_right (by omega)
    have targetCopies :
        finalCopies stem final = stem.count final + 1 := by
      unfold finalCopies
      exact Nat.min_eq_right small
    have normalEq :
        Order6FinalMarkerM2.finalNormalWord stem final =
          finalNormalWord stem final := by
      apply Word.toList_injective
      rw [Order6FinalMarkerM2.toList_finalNormalWord,
        toList_finalNormalWord]
      simp [Order6FinalMarkerM2.finalNormalList, finalNormalList,
        m2Copies, targetCopies]
    rw [normalEq] at m2Normal
    exact m2Normal
  · have m2Copies :
        Order6FinalMarkerM2.finalCopies stem final = 3 := by
      unfold Order6FinalMarkerM2.finalCopies
      exact Nat.min_eq_left (by omega)
    have targetCopies : finalCopies stem final = 2 := by
      unfold finalCopies
      exact Nat.min_eq_left (by omega)
    cases bodyShape :
        Order6FinalMarkerM2.removeLetter final stem with
    | nil =>
        have m2Shape :=
          m2FinalNormalWord_eq_block stem final 3 m2Copies bodyShape
        have targetShape :=
          finalNormalWord_eq_block stem final 2 targetCopies bodyShape
        rw [m2Shape] at m2Normal
        rw [targetShape]
        exact m2Normal.trans (derivesBlockThreeToTwo final)
    | cons head tail =>
        have m2Shape :=
          m2FinalNormalWord_eq_body_append
            stem final 3 m2Copies bodyShape
        have targetShape :=
          finalNormalWord_eq_body_append
            stem final 2 targetCopies bodyShape
        have contract :=
          Derives.prepend
            (S5_107.listWordOfCons head tail)
            (derivesBlockThreeToTwo final)
        rw [m2Shape] at m2Normal
        rw [targetShape]
        exact m2Normal.trans contract

private structure Prepared (source : Word Nat) where
  normal : Word Nat
  derivation : Derives basis source normal
  count_le_two : ∀ tested, normal.toList.count tested ≤ 2

/-- Build a final-marker-preserving, genuinely two-limited representative.
The body is normalized by the complete S5_110 normalizer behind the
protected terminal block. -/
private def prepareWord (source : Word Nat) : Prepared source := by
  let split := splitPrefixFinal source
  have reconstruct :
      wordOfPrefixFinal split.1 split.2 = source :=
    wordOfPrefixFinal_split source
  have gathered := derivesFinalNormal split.1 split.2
  rw [reconstruct] at gathered
  let copies := finalCopies split.1 split.2
  have copiesPositive : 0 < copies :=
    finalCopies_positive split.1 split.2
  have copiesUpper : copies ≤ 2 :=
    finalCopies_le_two split.1 split.2
  cases bodyShape :
      Order6FinalMarkerM2.removeLetter split.2 split.1 with
  | nil =>
      have normalShape :=
        finalNormalWord_eq_block
          split.1 split.2 copies rfl bodyShape
      rw [normalShape] at gathered
      exact
        { normal := finalBlockWord split.2 copies
          derivation := gathered
          count_le_two := fun tested =>
            finalBlock_count_le_two
              split.2 copies tested copiesPositive copiesUpper }
  | cons head tail =>
      let bodyWord := S5_107.listWordOfCons head tail
      let finalBlock := finalBlockWord split.2 copies
      have normalShape :
          finalNormalWord split.1 split.2 =
            bodyWord ++ finalBlock := by
        simpa [bodyWord, finalBlock] using
          finalNormalWord_eq_body_append
            split.1 split.2 copies rfl bodyShape
      rw [normalShape] at gathered
      have bodyCanonical :=
        S5_110Normalization.derivesCanonical bodyWord
      have bodyLifted :=
        liftS5_110DerivationWithSuffix bodyCanonical finalBlock
      have bodySignature :=
        S5_110.derives_sameSignature bodyCanonical
      have bodyFinalAbsent : split.2 ∉ bodyWord.toList := by
        change split.2 ∉ head :: tail
        rw [← bodyShape]
        simp [Order6FinalMarkerM2.removeLetter]
      have canonicalFinalAbsent :
          split.2 ∉
            (S5_110Syntax.canonicalWord bodyWord).toList := by
        intro member
        exact bodyFinalAbsent <|
          (bodySignature.support split.2).mpr member
      refine
        { normal := S5_110Syntax.canonicalWord bodyWord ++ finalBlock
          derivation := gathered.trans bodyLifted
          count_le_two := ?_ }
      intro tested
      rw [Word.toList_append, List.count_append]
      by_cases same : tested = split.2
      · subst tested
        have canonicalZero :
            (S5_110Syntax.canonicalWord bodyWord).toList.count split.2 =
              0 :=
          List.count_eq_zero.mpr canonicalFinalAbsent
        rw [canonicalZero, Nat.zero_add]
        exact finalBlock_count_le_two
          split.2 copies split.2 copiesPositive copiesUpper
      · have blockZero :
            finalBlock.toList.count tested = 0 := by
          unfold finalBlock
          rw [toList_finalBlockWord split.2 copies copiesPositive]
          exact count_replicate_of_ne same copies
        rw [blockZero, Nat.add_zero]
        exact canonicalWord_count_le_two bodyWord tested

private theorem sameSignatureOfDerivation
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_110Syntax.SameCappedSingletonSignature left right :=
  S5_110Invariant.sameSignature_of_s5_110_valid
    (Identity.mk left right)
    (fun valuation => derivation.sound s5Models valuation)

/-- On two-limited words the cap-two signature determines the cap-three
M2 data exactly. -/
private theorem m2DataOfTwoLimitedSignature
    {left right : Word Nat}
    (same : S5_110Syntax.SameCappedSingletonSignature left right)
    (leftBound : ∀ tested, left.toList.count tested ≤ 2)
    (rightBound : ∀ tested, right.toList.count tested ≤ 2) :
    Order6FinalMarkerM2.M2Data left right := by
  constructor
  · intro tested
    have exactCount := same.capped tested
    unfold S5_110Syntax.cappedMultiplicity at exactCount
    have leftExact :
        Nat.min 2 (left.toList.count tested) =
          left.toList.count tested :=
      Nat.min_eq_right (leftBound tested)
    have rightExact :
        Nat.min 2 (right.toList.count tested) =
          right.toList.count tested :=
      Nat.min_eq_right (rightBound tested)
    rw [leftExact, rightExact] at exactCount
    unfold S5_213Syntax.cappedMultiplicity
    have leftBoundThree : left.toList.count tested ≤ 3 :=
      Nat.le_trans (leftBound tested) (by decide)
    have rightBoundThree : right.toList.count tested ≤ 3 :=
      Nat.le_trans (rightBound tested) (by decide)
    have leftM2Exact :
        Nat.min 3 (left.toList.count tested) =
          left.toList.count tested :=
      Nat.min_eq_right leftBoundThree
    have rightM2Exact :
        Nat.min 3 (right.toList.count tested) =
          right.toList.count tested :=
      Nat.min_eq_right rightBoundThree
    rw [leftM2Exact, rightM2Exact]
    exact exactCount
  · exact same.singletonSequence_eq

/-- Unrestricted completeness of the displayed four laws for
`Id(S3_6) ∩ Id(S5_110)`. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (s3Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_6.table.semigroup)
    (s5Valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_110.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  let leftPrepared := prepareWord identity.lhs
  let rightPrepared := prepareWord identity.rhs
  have sourceSignature :=
    S5_110Invariant.sameSignature_of_s5_110_valid identity s5Valid
  have leftSignature :=
    sameSignatureOfDerivation leftPrepared.derivation
  have rightSignature :=
    sameSignatureOfDerivation rightPrepared.derivation
  have normalSignature :
      S5_110Syntax.SameCappedSingletonSignature
        leftPrepared.normal rightPrepared.normal :=
    S5_110Syntax.SameCappedSingletonSignature.trans
      (S5_110Syntax.SameCappedSingletonSignature.symm leftSignature)
      (S5_110Syntax.SameCappedSingletonSignature.trans
        sourceSignature rightSignature)
  have normalM2Data :
      Order6FinalMarkerM2.M2Data
        leftPrepared.normal rightPrepared.normal :=
    m2DataOfTwoLimitedSignature normalSignature
      leftPrepared.count_le_two rightPrepared.count_le_two
  let normalized : Identity Nat :=
    Identity.mk leftPrepared.normal rightPrepared.normal
  have normalizedMarkerValid :
      normalized.SatisfiedBy Generated.S3_6.table.semigroup := by
    intro valuation
    exact
      (leftPrepared.derivation.sound markerModels valuation).symm.trans <|
        (s3Valid valuation).trans
          (rightPrepared.derivation.sound markerModels valuation)
  have canonicalMarkerValid :
      normalized.SatisfiedBy finalMarkerThree.semigroup := by
    rw [SemigroupBasis.Generated.S3_6.table_eq_catalogue_model]
      at normalizedMarkerValid
    exact normalizedMarkerValid
  have m2Middle :
      Derives Order6FinalMarkerM2.basis
        leftPrepared.normal rightPrepared.normal := by
    simpa [normalized] using
      Order6FinalMarkerM2.derives_of_marker_m2Data
        normalized canonicalMarkerValid normalM2Data
  have middle : Derives basis
      leftPrepared.normal rightPrepared.normal :=
    m2Middle.transport m2AxiomDerives
  exact leftPrepared.derivation.trans <|
    middle.trans rightPrepared.derivation.symm

def intersectionBasis :
    IntersectionBasis Generated.S3_6.table.semigroup
      Generated.Catalogue.S5_110.table.semigroup basis where
  leftModels := markerModels
  rightModels := s5Models
  complete := derivesOfFactorValid

end SemigroupBasis.CoRoots.Order6FactorPairS3_6S5_110

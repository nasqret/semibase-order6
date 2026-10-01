import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83DirectStem
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_83Factors

/-!
# Unrestricted completeness for the direct `S3_16` / `S5_83` family

Every nonsingleton word first reaches a duplicate-free stem followed by its
terminal pair.  The `S5_83` terminal suffix then selects one of three shared
canonical forms:

* repeated final: two copies of the first-occurrence block;
* unique final but repeated penultimate: `F F t`;
* globally unique terminal pair: `F p t`.

The canonical form depends only on the first-occurrence sequence and the
`S5_83` terminal-unique suffix, so it works for both `S5_83` and `S5_84`.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct

open SemigroupBasis
open SemigroupBasis.Examples

private theorem firstOccurrenceSequence_eq_self_of_nodup
    {letters : List Nat} (nodup : letters.Nodup) :
    firstOccurrenceSequence letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      have data := List.nodup_cons.mp nodup
      rw [firstOccurrenceSequence, induction data.2]
      congr 1
      apply List.filter_eq_self.mpr
      intro next member
      exact decide_eq_true <| by
        intro equal
        subst next
        exact data.1 member

private theorem firstOccurrenceSequence_append_singleton
    (selected : Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters ++ [selected]) =
        if selected ∈ letters then
          firstOccurrenceSequence letters
        else
          firstOccurrenceSequence letters ++ [selected]
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_append_singleton selected rest
      by_cases equal : letter = selected
      · subst letter
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, member,
            List.filter_append]
      · have reverseEqual : selected ≠ letter := Ne.symm equal
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, equal, reverseEqual,
            member, List.filter_append]

private theorem firstOccurrenceSequence_append_of_subset :
    ∀ (right left : List Nat),
      (∀ letter, letter ∈ right → letter ∈ left) →
      firstOccurrenceSequence (left ++ right) =
        firstOccurrenceSequence left
  | [], left, _ => by simp
  | letter :: rest, left, subset => by
      have letterMember : letter ∈ left :=
        subset letter (List.Mem.head rest)
      have restSubset :
          ∀ tested, tested ∈ rest → tested ∈ left ++ [letter] := by
        intro tested member
        exact List.mem_append_left [letter] <|
          subset tested (List.Mem.tail letter member)
      calc
        firstOccurrenceSequence (left ++ letter :: rest) =
            firstOccurrenceSequence ((left ++ [letter]) ++ rest) := by
          simp [List.append_assoc]
        _ = firstOccurrenceSequence (left ++ [letter]) :=
          firstOccurrenceSequence_append_of_subset rest
            (left ++ [letter]) restSubset
        _ = firstOccurrenceSequence left := by
          rw [firstOccurrenceSequence_append_singleton,
            if_pos letterMember]

private theorem nodup_append_singleton
    {letters : List Nat} {letter : Nat}
    (nodup : letters.Nodup) (absent : letter ∉ letters) :
    (letters ++ [letter]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨nodup, by simp, ?_⟩
  intro left leftMember right rightMember equal
  have rightEq : right = letter := by simpa using rightMember
  subst right
  subst left
  exact absent leftMember

private instance instDecidableIsSingletonWord (word : Word Nat) :
    Decidable (SemigroupBasis.CoRoots.S5_83.IsSingletonWord word) := by
  unfold SemigroupBasis.CoRoots.S5_83.IsSingletonWord
  cases SemigroupBasis.CoRoots.S5_83.terminalSplit word <;>
    exact inferInstance

private def canonicalList (word : Word Nat) : List Nat :=
  let order := firstOccurrenceSequence word.toList
  let suffix := SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix word
  if SemigroupBasis.CoRoots.S5_83.IsSingletonWord word then
    order
  else
    match suffix with
    | [] => order ++ order
    | [final] => order.dropLast ++ order.dropLast ++ [final]
    | _ => order

private theorem canonicalList_eq_of_invariants
    {left right : Word Nat}
    (order :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (suffix :
      SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix left =
        SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix right)
    (singleton :
      SemigroupBasis.CoRoots.S5_83.IsSingletonWord left ↔
        SemigroupBasis.CoRoots.S5_83.IsSingletonWord right) :
    canonicalList left = canonicalList right := by
  unfold canonicalList
  rw [order, suffix]
  by_cases leftSingleton :
      SemigroupBasis.CoRoots.S5_83.IsSingletonWord left
  · have rightSingleton := singleton.mp leftSingleton
    simp [leftSingleton, rightSingleton]
  · have rightSingleton :
        ¬ SemigroupBasis.CoRoots.S5_83.IsSingletonWord right := by
      intro present
      exact leftSingleton (singleton.mpr present)
    simp [leftSingleton, rightSingleton]

private theorem listDerivesPairCanonical
    (stem : List Nat) (penultimate final : Nat)
    (nodup : stem.Nodup) :
    ListDerives
      (stem ++ [penultimate, final])
      (canonicalList
        (SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair
          stem penultimate final)) := by
  let normalWord :=
    SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair
      stem penultimate final
  have splitEq :
      SemigroupBasis.CoRoots.S5_83.terminalSplit normalWord =
        SemigroupBasis.CoRoots.S5_83.TerminalSplit.pair
          stem penultimate final := by
    exact
      SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord_inverse
        (SemigroupBasis.CoRoots.S5_83.TerminalSplit.pair
          stem penultimate final)
  have notSingleton :
      ¬ SemigroupBasis.CoRoots.S5_83.IsSingletonWord normalWord := by
    simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord, splitEq]
  change
    ListDerives
      (stem ++ [penultimate, final])
      (canonicalList normalWord)
  by_cases repeated : final = penultimate ∨ final ∈ stem
  · have suffixEmpty :
        SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix normalWord = [] := by
      simp [SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix,
        splitEq, repeated]
    by_cases penultimateMember : penultimate ∈ stem
    · have finalMember : final ∈ stem := by
        rcases repeated with equal | member
        · simpa [equal] using penultimateMember
        · exact member
      have subset :
          ∀ letter, letter ∈ [penultimate, final] → letter ∈ stem := by
        intro letter member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with equal | equal
        · exact equal ▸ penultimateMember
        · exact equal ▸ finalMember
      have orderEq :
          firstOccurrenceSequence normalWord.toList = stem := by
        calc
          firstOccurrenceSequence normalWord.toList =
              firstOccurrenceSequence
                (stem ++ [penultimate, final]) := by
            simp [normalWord,
              SemigroupBasis.CoRoots.S5_83.toList_wordOfTerminalPair]
          _ = firstOccurrenceSequence stem :=
            firstOccurrenceSequence_append_of_subset
              [penultimate, final] stem subset
          _ = stem := firstOccurrenceSequence_eq_self_of_nodup nodup
      have derives :=
        listDerivesRepeatedFinalCanonical
          stem penultimate final repeated
      have canonicalEq : canonicalList normalWord = stem ++ stem := by
        unfold canonicalList
        rw [if_neg notSingleton, suffixEmpty, orderEq]
      rw [canonicalEq]
      simpa [penultimateMember] using derives
    · let order := stem ++ [penultimate]
      have orderNodup : order.Nodup :=
        nodup_append_singleton nodup penultimateMember
      have finalMember : final ∈ order := by
        rcases repeated with equal | member
        · subst final
          simp [order]
        · exact List.mem_append_left [penultimate] member
      have orderEq :
          firstOccurrenceSequence normalWord.toList = order := by
        calc
          firstOccurrenceSequence normalWord.toList =
              firstOccurrenceSequence (order ++ [final]) := by
            simp [normalWord, order,
              SemigroupBasis.CoRoots.S5_83.toList_wordOfTerminalPair,
              List.append_assoc]
          _ = firstOccurrenceSequence order :=
            firstOccurrenceSequence_append_of_subset
              [final] order (by simpa using finalMember)
          _ = order :=
            firstOccurrenceSequence_eq_self_of_nodup orderNodup
      have derives :=
        listDerivesRepeatedFinalCanonical
          stem penultimate final repeated
      have canonicalEq : canonicalList normalWord = order ++ order := by
        unfold canonicalList
        rw [if_neg notSingleton, suffixEmpty, orderEq]
      rw [canonicalEq]
      simpa [penultimateMember, order] using derives
  · have finalParts : final ≠ penultimate ∧ final ∉ stem :=
      not_or.mp repeated
    by_cases penultimateMember : penultimate ∈ stem
    · have suffixEq :
          SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix normalWord =
            [final] := by
        simp [SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix,
          splitEq, repeated, penultimateMember]
      have finalAbsent : final ∉ stem ++ [penultimate] := by
        simp [finalParts.1, finalParts.2]
      have orderEq :
          firstOccurrenceSequence normalWord.toList = stem ++ [final] := by
        calc
          firstOccurrenceSequence normalWord.toList =
              firstOccurrenceSequence
                ((stem ++ [penultimate]) ++ [final]) := by
            simp [normalWord,
              SemigroupBasis.CoRoots.S5_83.toList_wordOfTerminalPair,
              List.append_assoc]
          _ = firstOccurrenceSequence (stem ++ [penultimate]) ++ [final] := by
            rw [firstOccurrenceSequence_append_singleton,
              if_neg finalAbsent]
          _ = firstOccurrenceSequence stem ++ [final] := by
            rw [firstOccurrenceSequence_append_singleton,
              if_pos penultimateMember]
          _ = stem ++ [final] := by
            rw [firstOccurrenceSequence_eq_self_of_nodup nodup]
      have derives :=
        listDerivesUniqueFinalCanonical
          stem penultimate final penultimateMember
      have canonicalEq :
          canonicalList normalWord = stem ++ stem ++ [final] := by
        unfold canonicalList
        rw [if_neg notSingleton, suffixEq, orderEq]
        simp [List.append_assoc]
      rw [canonicalEq]
      simpa [List.append_assoc] using derives
    · have suffixEq :
          SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix normalWord =
            [penultimate, final] := by
        simp [SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix,
          splitEq, repeated, penultimateMember]
      have stemPenultimateNodup :
          (stem ++ [penultimate]).Nodup :=
        nodup_append_singleton nodup penultimateMember
      have finalAbsent : final ∉ stem ++ [penultimate] := by
        simp [finalParts.1, finalParts.2]
      have fullNodup : (stem ++ [penultimate, final]).Nodup := by
        simpa [List.append_assoc] using
          nodup_append_singleton stemPenultimateNodup finalAbsent
      have orderEq :
          firstOccurrenceSequence normalWord.toList =
            stem ++ [penultimate, final] := by
        simpa [normalWord,
          SemigroupBasis.CoRoots.S5_83.toList_wordOfTerminalPair] using
            firstOccurrenceSequence_eq_self_of_nodup fullNodup
      have canonicalEq :
          canonicalList normalWord = stem ++ [penultimate, final] := by
        unfold canonicalList
        rw [if_neg notSingleton, suffixEq, orderEq]
      rw [canonicalEq]
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (stem ++ [penultimate, final])

private theorem derivesOfListDerivesToList
    {left right : Word Nat}
    (derivation : ListDerives left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

private theorem satisfiedBy_of_table_eq
    {source target : FiniteTable} (tableEq : source = target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy source.semigroup) :
    identity.SatisfiedBy target.semigroup := by
  cases tableEq
  exact valid

private theorem s3_16_firstOccurrences
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList :=
  SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
    identity <|
      satisfiedBy_of_table_eq
        SemigroupBasis.Generated.S3_16.table_eq_catalogue_model
        identity valid

private theorem derivesOfValid
    (right : Semigroup (Fin 5))
    (rightModels : Models right basis)
    (validSignature :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy right →
        SemigroupBasis.CoRoots.S5_83.SameTerminalUniqueSuffixSignature
          identity.lhs identity.rhs)
    (identity : Identity Nat)
    (initialValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid : identity.SatisfiedBy right) :
    Derives basis identity.lhs identity.rhs := by
  have originalSignature := validSignature identity finalValid
  cases leftSplitEq :
      SemigroupBasis.CoRoots.S5_83.terminalSplit identity.lhs with
  | singleton leftFinal =>
      cases rightSplitEq :
          SemigroupBasis.CoRoots.S5_83.terminalSplit identity.rhs with
      | pair rightStem rightPenultimate rightFinal =>
          have leftSingleton :
              SemigroupBasis.CoRoots.S5_83.IsSingletonWord identity.lhs := by
            simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
              leftSplitEq]
          have rightSingleton :=
            originalSignature.singleton.mp leftSingleton
          simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
            rightSplitEq] at rightSingleton
      | singleton rightFinal =>
          have leftUnique :
              SemigroupBasis.CoRoots.S5_83.UniqueFinal
                identity.lhs leftFinal := by
            simp [SemigroupBasis.CoRoots.S5_83.UniqueFinal, leftSplitEq]
          have rightUnique :=
            (originalSignature.uniqueFinal leftFinal).mp leftUnique
          have finalEq : rightFinal = leftFinal := by
            simpa [SemigroupBasis.CoRoots.S5_83.UniqueFinal,
              rightSplitEq] using rightUnique
          rw [← SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord
              identity.lhs,
            ← SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord
              identity.rhs,
            leftSplitEq, rightSplitEq, finalEq]
          exact Derives.refl _
  | pair leftStem leftPenultimate leftFinal =>
      cases rightSplitEq :
          SemigroupBasis.CoRoots.S5_83.terminalSplit identity.rhs with
      | singleton rightFinal =>
          have rightSingleton :
              SemigroupBasis.CoRoots.S5_83.IsSingletonWord identity.rhs := by
            simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
              rightSplitEq]
          have leftSingleton :=
            originalSignature.singleton.mpr rightSingleton
          simp [SemigroupBasis.CoRoots.S5_83.IsSingletonWord,
            leftSplitEq] at leftSingleton
      | pair rightStem rightPenultimate rightFinal =>
          let leftNormalStem := firstOccurrenceSequence leftStem
          let rightNormalStem := firstOccurrenceSequence rightStem
          let leftWord :=
            SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair
              leftNormalStem leftPenultimate leftFinal
          let rightWord :=
            SemigroupBasis.CoRoots.S5_83.wordOfTerminalPair
              rightNormalStem rightPenultimate rightFinal
          have leftDerives : Derives basis identity.lhs leftWord := by
            rw [← SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord
              identity.lhs, leftSplitEq]
            exact derivesStemNormal leftStem leftPenultimate leftFinal
          have rightDerives : Derives basis identity.rhs rightWord := by
            rw [← SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord
              identity.rhs, rightSplitEq]
            exact derivesStemNormal rightStem rightPenultimate rightFinal
          have normalizedInitialValid :
              (⟨leftWord, rightWord⟩ : Identity Nat).SatisfiedBy
                SemigroupBasis.Generated.S3_16.table.semigroup := by
            intro valuation
            have leftSound := leftDerives.sound modelsS3_16 valuation
            have rightSound := rightDerives.sound modelsS3_16 valuation
            exact leftSound.symm.trans <|
              (initialValid valuation).trans rightSound
          have normalizedFinalValid :
              (⟨leftWord, rightWord⟩ : Identity Nat).SatisfiedBy right := by
            intro valuation
            have leftSound := leftDerives.sound rightModels valuation
            have rightSound := rightDerives.sound rightModels valuation
            exact leftSound.symm.trans <|
              (finalValid valuation).trans rightSound
          have normalizedSignature :=
            validSignature
              (⟨leftWord, rightWord⟩ : Identity Nat)
              normalizedFinalValid
          have order :=
            s3_16_firstOccurrences
              (⟨leftWord, rightWord⟩ : Identity Nat)
              normalizedInitialValid
          have suffix := normalizedSignature.terminalUniqueSuffix_eq
          have canonicalEq : canonicalList leftWord = canonicalList rightWord :=
            canonicalList_eq_of_invariants
              order suffix normalizedSignature.singleton
          have leftCanonical :=
            listDerivesPairCanonical
              leftNormalStem leftPenultimate leftFinal
              (firstOccurrenceSequence_nodup leftStem)
          have rightCanonical :=
            listDerivesPairCanonical
              rightNormalStem rightPenultimate rightFinal
              (firstOccurrenceSequence_nodup rightStem)
          have middleList :
              ListDerives
                (leftNormalStem ++ [leftPenultimate, leftFinal])
                (rightNormalStem ++ [rightPenultimate, rightFinal]) :=
            leftCanonical.trans <| by
              rw [canonicalEq]
              exact rightCanonical.symm
          have middle : Derives basis leftWord rightWord := by
            apply derivesOfListDerivesToList
            simpa [leftWord, rightWord,
              SemigroupBasis.CoRoots.S5_83.toList_wordOfTerminalPair] using
                middleList
          exact leftDerives.trans <| middle.trans rightDerives.symm

theorem derivesOfS3_16S5_83Valid
    (identity : Identity Nat)
    (initialValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfValid
    SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
    modelsS5_83
    SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
    identity initialValid finalValid

theorem derivesOfS3_16S5_84Valid
    (identity : Identity Nat)
    (initialValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  derivesOfValid
    SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
    modelsS5_84
    SemigroupBasis.CoRoots.S5_83Factors.S5_84.valid_signature
    identity initialValid finalValid

def intersectionBasisS5_83 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup
      basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_83
  complete := derivesOfS3_16S5_83Valid

def intersectionBasisS5_84 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup
      basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_84
  complete := derivesOfS3_16S5_84Valid

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct

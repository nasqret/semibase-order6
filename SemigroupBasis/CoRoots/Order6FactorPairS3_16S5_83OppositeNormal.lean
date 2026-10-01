import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_530Normalization
import SemigroupBasis.CoRoots.S5_83Factors
import SemigroupBasis.CoRoots.S5_345Factors

/-!
Unrestricted normal-form completeness for the four-law
`S3_16` / `S5_83^op` factor intersection.

The proof reuses the `S5_530` first-occurrence block normalizer.  Its blocks
are first capped at two copies.  The two insertion laws then contract every
doubled block after the maximal globally-unique initial prefix of length at
most two.  The resulting representative is determined by:

* the first-occurrence sequence, recovered from `S3_16`;
* the initial globally-unique prefix, recovered as the reverse of the
  `S5_83` terminal-unique suffix on the reversed word.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite

open SemigroupBasis
open SemigroupBasis.Examples

abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## Transported first-occurrence block normalization -/

private theorem derivesS5Power :
    Derives basis
      SemigroupBasis.CoRoots.S5_530.s5_530XXX
      SemigroupBasis.CoRoots.S5_530.s5_530XXXX := by
  have extended :=
    Derives.appendRight derivesPowerLaw (Word.singleton 0)
  simpa [SemigroupBasis.CoRoots.S5_530.s5_530XXX,
    SemigroupBasis.CoRoots.S5_530.s5_530XXXX,
    powerLaw, xx, xxx, Word.singleton, Word.append,
    Word.append_assoc] using extended

private theorem derivesS5Gather :
    Derives basis
      SemigroupBasis.CoRoots.S5_530.s5_530XXY
      SemigroupBasis.CoRoots.S5_530.s5_530XYX := by
  simpa [SemigroupBasis.CoRoots.S5_530.s5_530XXY,
    SemigroupBasis.CoRoots.S5_530.s5_530XYX,
    returnLaw, xxy, xyx] using derivesReturnLaw

private theorem s5AxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ SemigroupBasis.CoRoots.S5_530.s5_530Basis) :
    Derives basis identity.lhs identity.rhs := by
  simp only [SemigroupBasis.CoRoots.S5_530.s5_530Basis,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact derivesS5Power
  · exact derivesS5Gather

/-! ## Cap-two first-occurrence blocks -/

/-- A flattened first-occurrence block list with block sizes one or two. -/
inductive CapNormal : List Nat → Prop
  | nil : CapNormal []
  | single (label : Nat) (tail : List Nat) :
      CapNormal tail → label ∉ tail → CapNormal (label :: tail)
  | double (label : Nat) (tail : List Nat) :
      CapNormal tail → label ∉ tail →
        CapNormal (label :: label :: tail)

private theorem capS5Normal
    {letters : List Nat}
    (normal : SemigroupBasis.CoRoots.S5_530.S5_530Normal letters) :
    ∃ capped,
      CapNormal capped ∧
      ListDerives letters capped ∧
      (∀ label, label ∈ capped ↔ label ∈ letters) := by
  induction normal with
  | nil =>
      exact ⟨[], .nil, .empty, by simp⟩
  | single label tail _ absent induction =>
      obtain ⟨capped, cappedNormal, derives, support⟩ := induction
      have cappedAbsent : label ∉ capped := by
        intro member
        exact absent ((support label).mp member)
      refine ⟨label :: capped,
        .single label capped cappedNormal cappedAbsent, ?_, ?_⟩
      · simpa using derives.prepend [label]
      · intro tested
        simp only [List.mem_cons]
        rw [support tested]
  | double label tail _ absent induction =>
      obtain ⟨capped, cappedNormal, derives, support⟩ := induction
      have cappedAbsent : label ∉ capped := by
        intro member
        exact absent ((support label).mp member)
      refine ⟨label :: label :: capped,
        .double label capped cappedNormal cappedAbsent, ?_, ?_⟩
      · simpa using derives.prepend [label, label]
      · intro tested
        simp only [List.mem_cons]
        rw [support tested]
  | triple label tail _ absent induction =>
      obtain ⟨capped, cappedNormal, derives, support⟩ := induction
      have cappedAbsent : label ∉ capped := by
        intro member
        exact absent ((support label).mp member)
      have normalizedTail :
          ListDerives
            (label :: label :: label :: tail)
            (label :: label :: label :: capped) := by
        simpa using derives.prepend [label, label, label]
      have contracted :
          ListDerives
            (label :: label :: label :: capped)
            (label :: label :: capped) := by
        have base := SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesThreeToTwo (Word.singleton label))
        simpa [Word.singleton, Word.append, Word.append_assoc] using
          base.append capped
      refine ⟨label :: label :: capped,
        .double label capped cappedNormal cappedAbsent,
        normalizedTail.trans contracted, ?_⟩
      intro tested
      simp [support tested]

/-- Every word reaches a cap-two first-occurrence block form. -/
theorem exists_capNormal (input : Word Nat) :
    ∃ head tail,
      CapNormal (head :: tail) ∧
      Derives basis input (wordOfCons head tail) := by
  have sourceNormal :=
    SemigroupBasis.CoRoots.S5_530.s5_530DerivesNormal input
  cases normalEq :
      SemigroupBasis.CoRoots.S5_530.s5_530NormalList input.toList with
  | nil =>
      rw [normalEq] at sourceNormal
      exact False.elim sourceNormal
  | cons normalHead normalTail =>
      rw [normalEq] at sourceNormal
      have transported :
          Derives basis input
            (SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons
              normalHead normalTail) :=
        sourceNormal.transport s5AxiomDerives
      have normalProof :
          SemigroupBasis.CoRoots.S5_530.S5_530Normal
            (normalHead :: normalTail) := by
        rw [← normalEq]
        exact
          SemigroupBasis.CoRoots.S5_530.s5_530NormalList_normal
            input.toList
      obtain ⟨capped, cappedNormal, capDerivation, _⟩ :=
        capS5Normal normalProof
      have cappedNonempty : capped ≠ [] :=
        capDerivation.target_ne_nil
      cases capped with
      | nil =>
          exact False.elim (cappedNonempty rfl)
      | cons head tail =>
          have cappedWord :
              Derives basis
                (SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons
                  normalHead normalTail)
                (wordOfCons head tail) := by
            simpa [SemigroupBasis.CoRoots.S5_530.s5_530WordOfCons,
              wordOfCons] using
                SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
                  capDerivation
          exact ⟨head, tail, cappedNormal,
            transported.trans cappedWord⟩

/-! ## The protected-prefix canonical representative -/

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem firstOccurrenceSequence_single
    {label : Nat} {tail : List Nat} (absent : label ∉ tail) :
    firstOccurrenceSequence (label :: tail) =
      label :: firstOccurrenceSequence tail := by
  simp only [firstOccurrenceSequence]
  congr 1
  apply List.filter_eq_self.mpr
  intro selected member
  simp only [decide_eq_true_eq]
  intro equal
  subst selected
  exact absent <|
    (mem_firstOccurrenceSequence_iff label tail).mp member

private theorem firstOccurrenceSequence_double
    {label : Nat} {tail : List Nat} (absent : label ∉ tail) :
    firstOccurrenceSequence (label :: label :: tail) =
      label :: firstOccurrenceSequence tail := by
  rw [firstOccurrenceSequence,
    firstOccurrenceSequence_single absent]
  simp
  intro selected member equal
  subst selected
  exact absent <|
    (mem_firstOccurrenceSequence_iff label tail).mp member

/-- The maximal globally-simple initial block, capped at two letters, on a
cap-normal list.  The definition is total for use in the canonical renderer. -/
def protectedPrefix : List Nat → List Nat
  | [] => []
  | [first] => [first]
  | first :: second :: [] =>
      if first = second then [] else [first, second]
  | first :: second :: third :: rest =>
      if first = second then []
      else if second = third then [first]
      else [first, second]

private theorem protectedPrefix_double
    (label : Nat) (tail : List Nat) :
    protectedPrefix (label :: label :: tail) = [] := by
  cases tail <;> simp [protectedPrefix]

private theorem protectedPrefix_single_single
    (first second : Nat) (tail : List Nat)
    (firstAbsent : first ∉ second :: tail)
    (secondAbsent : second ∉ tail) :
    protectedPrefix (first :: second :: tail) = [first, second] := by
  have firstNe : first ≠ second := by
    intro equal
    subst second
    exact firstAbsent (by simp)
  cases tail with
  | nil =>
      simp [protectedPrefix, firstNe]
  | cons third rest =>
      have secondNe : second ≠ third := by
        intro equal
        subst third
        exact secondAbsent (by simp)
      simp [protectedPrefix, firstNe, secondNe]

private theorem protectedPrefix_single_double
    (first second : Nat) (tail : List Nat)
    (firstAbsent : first ∉ second :: second :: tail) :
    protectedPrefix (first :: second :: second :: tail) = [first] := by
  have firstNe : first ≠ second := by
    intro equal
    subst second
    exact firstAbsent (by simp)
  simp [protectedPrefix, firstNe]

/-- The canonical cap-normal representative.  Once the protected prefix is
fixed, every later first-occurrence block is represented by one copy. -/
def canonicalList (letters : List Nat) : List Nat :=
  let order := firstOccurrenceSequence letters
  match protectedPrefix letters with
  | [] =>
      match order with
      | [] => []
      | head :: tail => head :: head :: tail
  | [_] =>
      match order with
      | [] => []
      | [head] => [head]
      | head :: second :: tail => head :: second :: second :: tail
  | _ => order

theorem canonicalList_eq_of_invariants
    {left right : List Nat}
    (order :
      firstOccurrenceSequence left = firstOccurrenceSequence right)
    (prefixEq : protectedPrefix left = protectedPrefix right) :
    canonicalList left = canonicalList right := by
  simp only [canonicalList]
  rw [order, prefixEq]

private theorem contractDoubleAfterTwo
    (first second : Nat) (prefixTail : List Nat)
    (label : Nat) (suffix : List Nat) :
    ListDerives
      ((first :: second :: prefixTail) ++ label :: label :: suffix)
      ((first :: second :: prefixTail) ++ label :: suffix) := by
  let secondPrefix :=
    SemigroupBasis.CoRoots.S5_107.listWordOfCons second prefixTail
  have contracted := derivesLongFinalContraction
    (Word.singleton first) secondPrefix (Word.singleton label)
  have withSuffix :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord contracted).append
      suffix
  simpa [secondPrefix,
    SemigroupBasis.CoRoots.S5_107.listWordOfCons,
    Word.singleton, Word.append, Word.append_assoc,
    List.append_assoc] using withSuffix

private theorem collapseAfterTwo
    (first second : Nat) (prefixTail : List Nat)
    {letters : List Nat} (normal : CapNormal letters) :
    ListDerives
      ((first :: second :: prefixTail) ++ letters)
      ((first :: second :: prefixTail) ++
        firstOccurrenceSequence letters) := by
  induction normal generalizing prefixTail with
  | nil =>
      simpa [firstOccurrenceSequence] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) (first :: second :: prefixTail))
  | single label tail _ absent induction =>
      have collapsed :=
        induction (prefixTail := prefixTail ++ [label])
      simpa [firstOccurrenceSequence_single absent,
        List.append_assoc] using collapsed
  | double label tail _ absent induction =>
      have firstStep :=
        contractDoubleAfterTwo
          first second prefixTail label tail
      have collapsed :=
        induction (prefixTail := prefixTail ++ [label])
      have secondStep :
          ListDerives
            ((first :: second :: prefixTail) ++ label :: tail)
            ((first :: second :: prefixTail) ++
              label :: firstOccurrenceSequence tail) := by
        simpa [List.append_assoc] using collapsed
      exact firstStep.trans <| by
        simpa [firstOccurrenceSequence_double absent] using secondStep

/-- Every cap-normal list derives to its protected-prefix representative. -/
theorem capNormal_derivesCanonical
    {letters : List Nat} (normal : CapNormal letters) :
    ListDerives letters (canonicalList letters) := by
  cases normal with
  | nil =>
      exact .empty
  | double label tail tailNormal absent =>
      have collapsed := collapseAfterTwo label label [] tailNormal
      simpa [canonicalList, protectedPrefix_double,
        firstOccurrenceSequence_double absent] using collapsed
  | single label tail tailNormal absent =>
      cases tailNormal with
      | nil =>
          simpa [canonicalList, protectedPrefix,
            firstOccurrenceSequence] using
              (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
                (basis := basis) [label])
      | single second rest restNormal secondAbsent =>
          have collapsed := collapseAfterTwo label second [] restNormal
          simpa [canonicalList,
            protectedPrefix_single_single
              label second rest absent secondAbsent,
            firstOccurrenceSequence_single absent,
            firstOccurrenceSequence_single secondAbsent] using collapsed
      | double second rest restNormal secondAbsent =>
          have collapsed :=
            collapseAfterTwo label second [second] restNormal
          simpa [canonicalList,
            protectedPrefix_single_double label second rest absent,
            firstOccurrenceSequence_single absent,
            firstOccurrenceSequence_double secondAbsent,
            List.append_assoc] using collapsed

/-! ## Semantic determination of the protected prefix -/

private theorem reverse_wordOfCons_pair
    (first second : Nat) (rest : List Nat) :
    (wordOfCons first (second :: rest)).reverse =
      (SemigroupBasis.CoRoots.S5_83.TerminalSplit.pair
        rest.reverse second first).renderWord := by
  apply Word.toList_injective
  rw [Word.toList_reverse,
    SemigroupBasis.CoRoots.S5_83.TerminalSplit.toList_renderWord]
  simp [wordOfCons,
    SemigroupBasis.CoRoots.S5_83.TerminalSplit.renderList,
    Word.toList, List.reverse_cons, List.append_assoc]

private theorem terminalUniqueSuffix_reverse_eq_protected :
    ∀ {letters : List Nat}, CapNormal letters →
      match letters with
      | [] => True
      | head :: tail =>
          SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix
              (wordOfCons head tail).reverse =
            (protectedPrefix letters).reverse
  | _, .nil => by
      trivial
  | _, .double label tail tailNormal absent => by
      change
        SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix
            (wordOfCons label (label :: tail)).reverse =
          (protectedPrefix (label :: label :: tail)).reverse
      rw [reverse_wordOfCons_pair]
      simp only [SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix,
        SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord_inverse]
      simp [protectedPrefix_double]
  | _, .single label tail tailNormal absent => by
      cases tailNormal with
      | nil =>
          rfl
      | single second rest restNormal secondAbsent =>
          have labelNe : label ≠ second := by
            intro equal
            subst second
            exact absent (by simp)
          have labelAbsent : label ∉ rest := by
            intro member
            exact absent (by simp [member])
          change
            SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix
                (wordOfCons label (second :: rest)).reverse =
              (protectedPrefix (label :: second :: rest)).reverse
          rw [reverse_wordOfCons_pair,
            protectedPrefix_single_single
              label second rest absent secondAbsent]
          simp only [SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix,
            SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord_inverse]
          simp [labelNe, labelAbsent, secondAbsent]
      | double second rest restNormal secondAbsent =>
          have labelNe : label ≠ second := by
            intro equal
            subst second
            exact absent (by simp)
          have labelAbsent : label ∉ rest := by
            intro member
            exact absent (by simp [member])
          change
            SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix
                (wordOfCons label (second :: second :: rest)).reverse =
              (protectedPrefix
                (label :: second :: second :: rest)).reverse
          rw [reverse_wordOfCons_pair,
            protectedPrefix_single_double label second rest absent]
          simp only [SemigroupBasis.CoRoots.S5_83.terminalUniqueSuffix,
            SemigroupBasis.CoRoots.S5_83.terminalSplit_renderWord_inverse]
          simp [labelNe, labelAbsent, secondAbsent]

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

private theorem s5_83Opposite_protectedPrefix
    (left right : Word Nat)
    (leftNormal : CapNormal left.toList)
    (rightNormal : CapNormal right.toList)
    (valid :
      (⟨left, right⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite) :
    protectedPrefix left.toList = protectedPrefix right.toList := by
  have reversedValid :
      (⟨left, right⟩ : Identity Nat).reversed.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      (⟨left, right⟩ : Identity Nat)
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup).mp valid
  have signature :=
    SemigroupBasis.CoRoots.S5_83Factors.S5_83.valid_signature
      (⟨left, right⟩ : Identity Nat).reversed reversedValid
  have suffixes := signature.terminalUniqueSuffix_eq
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          have leftRelation :=
            terminalUniqueSuffix_reverse_eq_protected
              (letters := leftHead :: leftTail) <| by
                simpa [Word.toList] using leftNormal
          have rightRelation :=
            terminalUniqueSuffix_reverse_eq_protected
              (letters := rightHead :: rightTail) <| by
                simpa [Word.toList] using rightNormal
          have reversedPrefixes :
              (protectedPrefix (leftHead :: leftTail)).reverse =
                (protectedPrefix (rightHead :: rightTail)).reverse :=
            leftRelation.symm.trans <| suffixes.trans rightRelation
          have restored := congrArg List.reverse reversedPrefixes
          simpa [Word.toList] using restored

/-! ## Unrestricted intersection completeness -/

theorem derivesOfS3_16S5_83OppositeValid
    (identity : Identity Nat)
    (initialValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S3_16.table.semigroup)
    (finalValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨leftHead, leftTail, leftNormal, leftDerives⟩ :=
    exists_capNormal identity.lhs
  obtain ⟨rightHead, rightTail, rightNormal, rightDerives⟩ :=
    exists_capNormal identity.rhs
  let leftWord := wordOfCons leftHead leftTail
  let rightWord := wordOfCons rightHead rightTail
  have normalizedInitialValid :
      (⟨leftWord, rightWord⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup := by
    intro valuation
    have leftSound := leftDerives.sound modelsS3_16 valuation
    have rightSound := rightDerives.sound modelsS3_16 valuation
    exact leftSound.symm.trans <| (initialValid valuation).trans rightSound
  have normalizedFinalValid :
      (⟨leftWord, rightWord⟩ : Identity Nat).SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite := by
    intro valuation
    have leftSound := leftDerives.sound modelsS5_83Opposite valuation
    have rightSound := rightDerives.sound modelsS5_83Opposite valuation
    exact leftSound.symm.trans <| (finalValid valuation).trans rightSound
  have order := s3_16_firstOccurrences
    (⟨leftWord, rightWord⟩ : Identity Nat) normalizedInitialValid
  have prefixEq := s5_83Opposite_protectedPrefix
    leftWord rightWord
    (by simpa [leftWord, wordOfCons, Word.toList] using leftNormal)
    (by simpa [rightWord, wordOfCons, Word.toList] using rightNormal)
    normalizedFinalValid
  have canonicalEq :
      canonicalList (leftHead :: leftTail) =
        canonicalList (rightHead :: rightTail) :=
    canonicalList_eq_of_invariants
      (by simpa [leftWord, rightWord, wordOfCons, Word.toList] using order)
      (by simpa [leftWord, rightWord, wordOfCons, Word.toList] using prefixEq)
  have leftCanonical := capNormal_derivesCanonical leftNormal
  have rightCanonical := capNormal_derivesCanonical rightNormal
  have middleList :
      ListDerives
        (leftHead :: leftTail) (rightHead :: rightTail) :=
    leftCanonical.trans <| by
      rw [canonicalEq]
      exact rightCanonical.symm
  have middle : Derives basis leftWord rightWord := by
    simpa [leftWord, rightWord, wordOfCons] using
      SemigroupBasis.CoRoots.S5_107.ListDerives.toWord middleList
  exact leftDerives.trans <| middle.trans rightDerives.symm

/-- The four laws form an unrestricted basis for
`Id(S3_16) ∩ Id(S5_83^op)`. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite
      basis where
  leftModels := modelsS3_16
  rightModels := modelsS5_83Opposite
  complete := derivesOfS3_16S5_83OppositeValid

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite

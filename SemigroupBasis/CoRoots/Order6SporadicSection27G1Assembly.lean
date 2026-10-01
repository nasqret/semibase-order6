import SemigroupBasis.CoRoots.Order6SporadicSection27BetaNormalization
import SemigroupBasis.CoRoots.Order6SporadicSection27F9CertificateExtraction
import SemigroupBasis.CoRoots.S5_870Invariant

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev G1Table : FiniteTable :=
  SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561.table

private abbrev G1Separator : BetaSeparator G1Table.semigroup :=
  SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561.betaSeparator

private abbrev ListDerives := S5_107.ListDerives basis

/-!
## Target-specific semantic adapter for direct G1/S6_13561

The normalization and least-differing-block extraction are table-free and
are reused from the F9 proof.  Only the finite separator calculation below
is specific to G1.
-/

theorem g1_ordinary_ordinary :
    G1Table.semigroup.mul G1Separator.ordinary G1Separator.ordinary =
      G1Separator.ordinary := by
  decide

def g1ZoneValuation
    (ordinaryZone : List Nat) (activeLetter : Nat)
    (bridgeZone : List Nat) (letter : Nat) : Fin 6 :=
  if letter ∈ ordinaryZone then G1Separator.ordinary
  else if letter = activeLetter then G1Separator.active
  else if letter ∈ bridgeZone then G1Separator.bridge
  else G1Separator.fresh

theorem g1ZoneValuation_of_ordinary
    (ordinaryZone bridgeZone : List Nat) (activeLetter letter : Nat)
    (member : letter ∈ ordinaryZone) :
    g1ZoneValuation ordinaryZone activeLetter bridgeZone letter =
      G1Separator.ordinary := by
  simp [g1ZoneValuation, member]

theorem g1ZoneValuation_of_active
    (ordinaryZone bridgeZone : List Nat) (activeLetter : Nat)
    (absent : activeLetter ∉ ordinaryZone) :
    g1ZoneValuation ordinaryZone activeLetter bridgeZone activeLetter =
      G1Separator.active := by
  simp [g1ZoneValuation, absent]

theorem g1ZoneValuation_of_bridge
    (ordinaryZone bridgeZone : List Nat) (activeLetter letter : Nat)
    (ordinaryAbsent : letter ∉ ordinaryZone)
    (activeNe : letter ≠ activeLetter)
    (member : letter ∈ bridgeZone) :
    g1ZoneValuation ordinaryZone activeLetter bridgeZone letter =
      G1Separator.bridge := by
  simp [g1ZoneValuation, ordinaryAbsent, activeNe, member]

theorem g1ZoneValuation_of_fresh
    (ordinaryZone bridgeZone : List Nat) (activeLetter letter : Nat)
    (ordinaryAbsent : letter ∉ ordinaryZone)
    (activeNe : letter ≠ activeLetter)
    (bridgeAbsent : letter ∉ bridgeZone) :
    g1ZoneValuation ordinaryZone activeLetter bridgeZone letter =
      G1Separator.fresh := by
  simp [g1ZoneValuation, ordinaryAbsent, activeNe, bridgeAbsent]

private theorem g1_foldl_all_ordinary
    (valuation : Nat → Fin 6) :
    ∀ (letters : List Nat),
      (∀ letter, letter ∈ letters →
        valuation letter = G1Separator.ordinary) →
      letters.foldl
          (fun current letter =>
            G1Table.semigroup.mul current (valuation letter))
          G1Separator.ordinary =
        G1Separator.ordinary
  | [], _ => rfl
  | letter :: rest, allOrdinary => by
      have letterOrdinary :
          valuation letter = G1Separator.ordinary :=
        allOrdinary letter (List.Mem.head rest)
      have restOrdinary :
          ∀ tested, tested ∈ rest →
            valuation tested = G1Separator.ordinary := by
        intro tested member
        exact allOrdinary tested (List.Mem.tail letter member)
      simp only [List.foldl_cons, letterOrdinary,
        g1_ordinary_ordinary]
      exact g1_foldl_all_ordinary valuation rest restOrdinary

private theorem g1_foldl_all_bridge_from_active
    (valuation : Nat → Fin 6) :
    ∀ (letters : List Nat),
      (∀ letter, letter ∈ letters →
        valuation letter = G1Separator.bridge) →
      letters.foldl
          (fun current letter =>
            G1Table.semigroup.mul current (valuation letter))
          G1Separator.active =
        G1Separator.active
  | [], _ => rfl
  | letter :: rest, allBridge => by
      have letterBridge : valuation letter = G1Separator.bridge :=
        allBridge letter (List.Mem.head rest)
      have restBridge :
          ∀ tested, tested ∈ rest →
            valuation tested = G1Separator.bridge := by
        intro tested member
        exact allBridge tested (List.Mem.tail letter member)
      simp only [List.foldl_cons, letterBridge,
        G1Separator.active_bridge]
      exact g1_foldl_all_bridge_from_active valuation rest restBridge

theorem g1_eval_casePrefixWord
    (valuation : Nat → Fin 6)
    (ordinaryZone : List Nat) (activeLetter : Nat)
    (bridgeZone : List Nat)
    (ordinaryValues :
      ∀ letter, letter ∈ ordinaryZone →
        valuation letter = G1Separator.ordinary)
    (activeValue : valuation activeLetter = G1Separator.active)
    (bridgeValues :
      ∀ letter, letter ∈ bridgeZone →
        valuation letter = G1Separator.bridge) :
    G1Table.semigroup.eval valuation
        (f9CasePrefixWord ordinaryZone activeLetter bridgeZone) =
      G1Separator.active := by
  cases ordinaryZone with
  | nil =>
      change
        bridgeZone.foldl
            (fun current letter =>
              G1Table.semigroup.mul current (valuation letter))
            (valuation activeLetter) =
          G1Separator.active
      rw [activeValue]
      exact g1_foldl_all_bridge_from_active
        valuation bridgeZone bridgeValues
  | cons head tail =>
      have headOrdinary : valuation head = G1Separator.ordinary :=
        ordinaryValues head (List.Mem.head tail)
      have tailOrdinary :
          ∀ letter, letter ∈ tail →
            valuation letter = G1Separator.ordinary := by
        intro letter member
        exact ordinaryValues letter (List.Mem.tail head member)
      change
        (tail ++ activeLetter :: bridgeZone).foldl
            (fun current letter =>
              G1Table.semigroup.mul current (valuation letter))
            (valuation head) =
          G1Separator.active
      rw [headOrdinary, List.foldl_append,
        g1_foldl_all_ordinary valuation tail tailOrdinary]
      simp only [List.foldl_cons, activeValue,
        G1Separator.ordinary_active]
      exact g1_foldl_all_bridge_from_active
        valuation bridgeZone bridgeValues

namespace F9Case1Data

/-- The table-free Case-1 payload yields a countervaluation in G1. -/
theorem g1_not_satisfiedBy
    {left right : Word Nat} (data : F9Case1Data left right) :
    ¬ (Identity.mk left right).SatisfiedBy G1Table.semigroup := by
  let valuation :=
    g1ZoneValuation data.ordinaryZone data.activeLetter []
  have prefixActive :
      G1Table.semigroup.eval valuation
          (f9CasePrefixWord data.ordinaryZone data.activeLetter []) =
        G1Separator.active := by
    apply g1_eval_casePrefixWord
    · intro letter member
      exact g1ZoneValuation_of_ordinary
        data.ordinaryZone [] data.activeLetter letter member
    · exact g1ZoneValuation_of_active
        data.ordinaryZone [] data.activeLetter data.activeAbsent
    · intro letter member
      simp at member
  have killedValue :
      valuation data.killed = G1Separator.active ∨
        valuation data.killed = G1Separator.ordinary := by
    rcases data.killedZone with ordinary | active
    · exact Or.inr <| g1ZoneValuation_of_ordinary
        data.ordinaryZone [] data.activeLetter data.killed ordinary
    · exact Or.inl <| by
        rw [active]
        exact g1ZoneValuation_of_active
          data.ordinaryZone [] data.activeLetter data.activeAbsent
  have leftFresh :
      valuation data.leftTail.head = G1Separator.fresh :=
    g1ZoneValuation_of_fresh
      data.ordinaryZone [] data.activeLetter data.leftTail.head
      data.leftTailOutside.1 data.leftTailOutside.2 (by simp)
  have rightFresh :
      valuation data.rightTail.head = G1Separator.fresh :=
    g1ZoneValuation_of_fresh
      data.ordinaryZone [] data.activeLetter data.rightTail.head
      data.rightTailOutside.1 data.rightTailOutside.2 (by simp)
  have values :
      G1Table.semigroup.eval valuation
          (left ++ Word.singleton data.freshLetter) = G1Separator.hit ∧
        G1Table.semigroup.eval valuation
          (right ++ Word.singleton data.freshLetter) =
            G1Separator.miss := by
    rw [data.leftExtended_eq, data.rightExtended_eq]
    exact BetaSeparator.eval_kill_vs_empty G1Separator
      valuation
      (f9CasePrefixWord data.ordinaryZone data.activeLetter [])
      data.leftTail data.rightTail data.killed prefixActive killedValue
      leftFresh rightFresh
  intro valid
  have extendedEqual :
      G1Table.semigroup.eval valuation
          (left ++ Word.singleton data.freshLetter) =
        G1Table.semigroup.eval valuation
          (right ++ Word.singleton data.freshLetter) := by
    rw [Semigroup.eval_append, Semigroup.eval_append, valid valuation]
  exact G1Separator.hit_ne_miss <|
    values.1.symm.trans (extendedEqual.trans values.2)

end F9Case1Data

namespace F9BridgeCaseData

/-- The table-free bridge payload yields a countervaluation in G1. -/
theorem g1_not_satisfiedBy
    {left right : Word Nat} (data : F9BridgeCaseData left right) :
    ¬ (Identity.mk left right).SatisfiedBy G1Table.semigroup := by
  let valuation :=
    g1ZoneValuation data.ordinaryZone data.activeLetter data.bridgeZone
  have prefixActive :
      G1Table.semigroup.eval valuation
          (f9CasePrefixWord data.ordinaryZone data.activeLetter
            data.bridgeZone) =
        G1Separator.active := by
    apply g1_eval_casePrefixWord
    · intro letter member
      exact g1ZoneValuation_of_ordinary
        data.ordinaryZone data.bridgeZone data.activeLetter letter member
    · exact g1ZoneValuation_of_active
        data.ordinaryZone data.bridgeZone data.activeLetter
        data.activeAbsent
    · intro letter member
      exact g1ZoneValuation_of_bridge
        data.ordinaryZone data.bridgeZone data.activeLetter letter
        (data.bridgeDisjoint letter member).1
        (data.bridgeDisjoint letter member).2 member
  have killedValue :
      valuation data.killed = G1Separator.active ∨
        valuation data.killed = G1Separator.ordinary := by
    rcases data.killedZone with ordinary | active
    · exact Or.inr <| g1ZoneValuation_of_ordinary
        data.ordinaryZone data.bridgeZone data.activeLetter
        data.killed ordinary
    · exact Or.inl <| by
        rw [active]
        exact g1ZoneValuation_of_active
          data.ordinaryZone data.bridgeZone data.activeLetter
          data.activeAbsent
  have preservedValue :
      valuation data.preserved = G1Separator.bridge :=
    g1ZoneValuation_of_bridge
      data.ordinaryZone data.bridgeZone data.activeLetter data.preserved
      (data.bridgeDisjoint data.preserved data.preservedBridge).1
      (data.bridgeDisjoint data.preserved data.preservedBridge).2
      data.preservedBridge
  have leftFresh :
      valuation data.leftTail.head = G1Separator.fresh :=
    g1ZoneValuation_of_fresh
      data.ordinaryZone data.bridgeZone data.activeLetter data.leftTail.head
      data.leftTailOutside.1 data.leftTailOutside.2.1
      data.leftTailOutside.2.2
  have rightFresh :
      valuation data.rightTail.head = G1Separator.fresh :=
    g1ZoneValuation_of_fresh
      data.ordinaryZone data.bridgeZone data.activeLetter data.rightTail.head
      data.rightTailOutside.1 data.rightTailOutside.2.1
      data.rightTailOutside.2.2
  have values :
      G1Table.semigroup.eval valuation
          (left ++ Word.singleton data.freshLetter) = G1Separator.hit ∧
        G1Table.semigroup.eval valuation
          (right ++ Word.singleton data.freshLetter) =
            G1Separator.miss := by
    rw [data.leftExtended_eq, data.rightExtended_eq]
    exact BetaSeparator.eval_kill_vs_bridge G1Separator
      valuation
      (f9CasePrefixWord data.ordinaryZone data.activeLetter
        data.bridgeZone)
      data.leftTail data.rightTail data.killed data.preserved
      prefixActive killedValue preservedValue leftFresh rightFresh
  intro valid
  have extendedEqual :
      G1Table.semigroup.eval valuation
          (left ++ Word.singleton data.freshLetter) =
        G1Table.semigroup.eval valuation
          (right ++ Word.singleton data.freshLetter) := by
    rw [Semigroup.eval_append, Semigroup.eval_append, valid valuation]
  exact G1Separator.hit_ne_miss <|
    values.1.symm.trans (extendedEqual.trans values.2)

end F9BridgeCaseData

/-- Every identity valid in G1 preserves the gap-block marker sequence. -/
theorem g1_valid_firstOccurrenceSequenceList_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy G1Table.semigroup) :
    firstOccurrenceSequenceList identity.lhs.toList =
      firstOccurrenceSequenceList identity.rhs.toList := by
  have standard :=
    SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561.valid_firstOccurrenceSequence_eq
      identity valid
  simpa only [firstOccurrenceSequenceList_eq_firstOccurrenceSequence]
    using standard

/-- The shared literal Cases 1/2/3 force uniqueness of G1-valid beta forms. -/
theorem g1_betaCanonicalBlocks_eq_of_valid
    {leftBlocks rightBlocks : List FirstOccurrenceGapBlock}
    {leftWord rightWord : Word Nat}
    (leftCanonical : BetaCanonicalBlocks leftBlocks)
    (rightCanonical : BetaCanonicalBlocks rightBlocks)
    (leftRendered : renderGapBlocks leftBlocks = leftWord.toList)
    (rightRendered : renderGapBlocks rightBlocks = rightWord.toList)
    (sameMarkers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks)
    (valid :
      (Identity.mk leftWord rightWord).SatisfiedBy G1Table.semigroup) :
    leftBlocks = rightBlocks := by
  apply Classical.byContradiction
  intro different
  rcases f9PaperCasesExtracted
      leftCanonical rightCanonical leftRendered rightRendered
      sameMarkers different with
    ⟨leftCaseOne⟩ | ⟨rightCaseOne⟩ | ⟨leftBridge⟩ | ⟨rightBridge⟩
  · rcases leftCaseOne with ⟨leftCaseOne⟩
    exact leftCaseOne.g1_not_satisfiedBy valid
  · rcases rightCaseOne with ⟨rightCaseOne⟩
    apply rightCaseOne.g1_not_satisfiedBy
    intro valuation
    exact (valid valuation).symm
  · rcases leftBridge with ⟨leftBridge⟩
    exact leftBridge.g1_not_satisfiedBy valid
  · rcases rightBridge with ⟨rightBridge⟩
    apply rightBridge.g1_not_satisfiedBy
    intro valuation
    exact (valid valuation).symm

private theorem g1NormalizeWord (word : Word Nat) :
    ∃ (blocks : List FirstOccurrenceGapBlock) (target : Word Nat),
      BetaCanonicalBlocks blocks ∧
        gapBlockMarkers blocks =
          firstOccurrenceSequenceList word.toList ∧
        renderGapBlocks blocks = target.toList ∧
        Derives basis word target := by
  rcases word with ⟨head, tail⟩
  obtain ⟨blocks, canonical, markers, derivation⟩ :=
    listDerivesToBetaCanonicalBlocks (head :: tail)
  obtain ⟨targetHead, targetTail, targetShape, wordDerivation⟩ :=
    S5_107.ListDerives.from_cons derivation
  refine ⟨blocks, S5_107.listWordOfCons targetHead targetTail,
    canonical, markers, ?_, ?_⟩
  · simpa [S5_107.listWordOfCons, Word.toList] using targetShape
  · simpa [S5_107.listWordOfCons] using wordDerivation

/-- Unrestricted completeness of the direct G1/S6_13561 basis. -/
theorem g1_basisFor : BasisFor G1Table.semigroup basis := by
  refine ⟨
    SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561.models,
    ?_⟩
  intro identity valid
  obtain ⟨leftBlocks, leftTarget, leftCanonical, leftMarkers,
      leftRendered, leftDerivation⟩ := g1NormalizeWord identity.lhs
  obtain ⟨rightBlocks, rightTarget, rightCanonical, rightMarkers,
      rightRendered, rightDerivation⟩ := g1NormalizeWord identity.rhs
  have sameFirstOccurrences :=
    g1_valid_firstOccurrenceSequenceList_eq identity valid
  have sameMarkers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks :=
    leftMarkers.trans <| sameFirstOccurrences.trans rightMarkers.symm
  have targetValid :
      (Identity.mk leftTarget rightTarget).SatisfiedBy G1Table.semigroup := by
    intro valuation
    exact
      (leftDerivation.sound
          SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561.models
          valuation).symm.trans <|
        (valid valuation).trans <|
          rightDerivation.sound
            SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561.models
            valuation
  have sameBlocks :=
    g1_betaCanonicalBlocks_eq_of_valid
      leftCanonical rightCanonical leftRendered rightRendered
      sameMarkers targetValid
  have sameTarget : leftTarget = rightTarget := by
    apply Word.toList_injective
    calc
      leftTarget.toList = renderGapBlocks leftBlocks := leftRendered.symm
      _ = renderGapBlocks rightBlocks := congrArg renderGapBlocks sameBlocks
      _ = rightTarget.toList := rightRendered
  have back : Derives basis leftTarget identity.rhs := by
    simpa only [sameTarget] using rightDerivation.symm
  exact leftDerivation.trans back

end SemigroupBasis.CoRoots.Order6SporadicSection27

namespace SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561

theorem representative_basis :
    SemigroupBasis.BasisFor table.semigroup
      SemigroupBasis.CoRoots.Order6SporadicSection27.basis :=
  SemigroupBasis.CoRoots.Order6SporadicSection27.g1_basisFor

theorem opposite_basis :
    SemigroupBasis.BasisFor table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6SporadicSection27.oppositeBasis := by
  simpa only [SemigroupBasis.CoRoots.Order6SporadicSection27.oppositeBasis]
    using (SemigroupBasis.BasisFor.oppositeReversed representative_basis)

end SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13561

import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090StableScannerStateDecomposition

/-!
# Prefix-generalized rank-090 stable scanner / signature agreement

This module follows fable's exact `msg-0293` cut and reuses codex-0's
independently kernel-green four-coordinate scanner-state decomposition.
Every additional state relation is proved before any owner intersection,
class endpoint, or recording carrier is claimed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.FirstOrderSuccessorBridge

universe u v

/-- Streaming form of the stable scanner, with its honest pending-block bit. -/
def stableStreamingFold
    (whole seen : List Nat) (afterSimple : Bool) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if whole.count letter = 1 then
        letter :: stableStreamingFold whole seen true rest
      else if letter ∈ seen ∧ afterSimple = false then
        stableStreamingFold whole seen false rest
      else
        [letter, letter] ++
          stableStreamingFold whole (seen ++ [letter]) false rest

/-- Emit the pending simple block immediately; the four-coordinate state
is retained exactly in the streaming prefix and `afterSimple` bit. -/
theorem stableScannerFold_eq_streaming
    (whole : List Nat) :
    ∀ (remaining current seen : List Nat),
      stableScannerFold whole seen current remaining =
        current.reverse ++
          stableStreamingFold whole seen (decide (current ≠ [])) remaining
  | [], current, _ => by
      simp [stableScannerFold, stableStreamingFold]
  | letter :: rest, current, seen => by
      by_cases simple : whole.count letter = 1
      · have tail := stableScannerFold_eq_streaming
          whole rest (letter :: current) seen
        simpa [stableScannerFold, stableStreamingFold, simple,
          List.reverse_cons, List.append_assoc] using tail
      · by_cases currentEmpty : current = []
        · subst current
          by_cases present : letter ∈ seen
          · simpa [stableScannerFold, stableStreamingFold,
              simple, present] using
                stableScannerFold_eq_streaming whole rest [] seen
          · simpa [stableScannerFold, stableStreamingFold,
              simple, present] using
                stableScannerFold_eq_streaming whole rest []
                  (seen ++ [letter])
        · have noDrop : ¬ (current = [] ∧ letter ∈ seen) := by
            intro impossible
            exact currentEmpty impossible.1
          have tail :=
            stableScannerFold_eq_streaming whole rest []
              (seen ++ [letter])
          have appended := congrArg
            (fun output : List Nat =>
              current.reverse ++ [letter, letter] ++ output) tail
          simpa [stableScannerFold, stableStreamingFold, simple,
            currentEmpty, noDrop, List.append_assoc] using appended

/-- Empty streaming state is literally the owner's proved stable canonical. -/
theorem stableStreamingFold_eq_ownerCanonical
    (letters : List Nat) :
    stableStreamingFold letters [] false letters =
      firstOrderSuccessorCanonicalList letters := by
  have folded := stableScannerFold_eq_streaming letters letters [] []
  simpa using folded.symm.trans
    (stableScannerFold_eq_ownerCanonical letters)

/-- Left-to-right first-occurrence extraction with an arbitrary prefix. -/
def firstOccurrenceAfterPrefix
    (seen : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ seen then
        firstOccurrenceAfterPrefix seen rest
      else
        letter :: firstOccurrenceAfterPrefix (letter :: seen) rest

/-- State extraction is precisely the original first-order list filtered
by the already-scanned prefix support. -/
theorem firstOccurrenceAfterPrefix_eq_filter
    (seen : List Nat) :
    ∀ remaining : List Nat,
      firstOccurrenceAfterPrefix seen remaining =
        (firstOccurrenceSequence remaining).filter
          (fun letter => decide (letter ∉ seen))
  | [] => by
      simp [firstOccurrenceAfterPrefix, firstOccurrenceSequence]
  | letter :: rest => by
      by_cases known : letter ∈ seen
      · rw [firstOccurrenceAfterPrefix, if_pos known,
          firstOccurrenceAfterPrefix_eq_filter seen rest]
        simp only [firstOccurrenceSequence, List.filter_cons,
          decide_eq_true_eq, known, not_true_eq_false, if_false]
        rw [List.filter_filter]
        apply List.filter_congr
        intro candidate _
        by_cases same : candidate = letter
        · subst candidate
          simp [known]
        · simp [same]
      · rw [firstOccurrenceAfterPrefix, if_neg known,
          firstOccurrenceAfterPrefix_eq_filter (letter :: seen) rest]
        simp only [firstOccurrenceSequence, List.filter_cons,
          decide_eq_true_eq, known, not_false_eq_true, if_true]
        congr 1
        rw [List.filter_filter]
        apply List.filter_congr
        intro candidate _
        by_cases same : candidate = letter
        · subst candidate
          simp
        · simp [same]

/-- The empty-prefix state recovers the complete canonical first order. -/
theorem firstOccurrenceAfterPrefix_nil
    (letters : List Nat) :
    firstOccurrenceAfterPrefix [] letters =
      firstOccurrenceSequence letters := by
  rw [firstOccurrenceAfterPrefix_eq_filter]
  apply List.filter_eq_self.mpr
  intro letter _
  simp

/-- A globally simple source has at most one actual immediate target. -/
theorem adjacent_target_unique_of_count_one
    (source : Nat) :
    ∀ (letters : List Nat) (leftTarget rightTarget : Nat),
      letters.count source = 1 →
      (source, leftTarget) ∈
        SemigroupBasis.CoRoots.S5_107.listAdjacentPairs letters →
      (source, rightTarget) ∈
        SemigroupBasis.CoRoots.S5_107.listAdjacentPairs letters →
      leftTarget = rightTarget
  | [], _, _, _, leftEdge, _ => by
      simp at leftEdge
  | [_], _, _, _, leftEdge, _ => by
      simp at leftEdge
  | first :: second :: rest,
      leftTarget, rightTarget, countOne, leftEdge, rightEdge => by
      simp only [SemigroupBasis.CoRoots.S5_107.listAdjacentPairs_cons_cons,
        List.mem_cons, Prod.mk.injEq] at leftEdge rightEdge
      by_cases firstSource : first = source
      · subst first
        have tailAbsent : source ∉ second :: rest := by
          apply List.count_eq_zero.mp
          simp only [List.count_cons_self] at countOne
          omega
        have noTail :
            ∀ target,
              (source, target) ∉
                SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
                  (second :: rest) := by
          intro target edge
          obtain ⟨before, after, split⟩ :=
            (SemigroupBasis.CoRoots.S5_107.mem_listAdjacentPairs_iff_exists_split
              source target (second :: rest)).mp edge
          apply tailAbsent
          rw [split]
          simp
        rcases leftEdge with leftFirst | leftTail
        · rcases rightEdge with rightFirst | rightTail
          · exact leftFirst.2.trans rightFirst.2.symm
          · exact False.elim (noTail rightTarget rightTail)
        · exact False.elim (noTail leftTarget leftTail)
      · have tailCount : (second :: rest).count source = 1 := by
          simpa [firstSource] using countOne
        have leftTail :
            (source, leftTarget) ∈
              SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
                (second :: rest) := by
          rcases leftEdge with leftFirst | leftTail
          · exact False.elim (firstSource leftFirst.1.symm)
          · exact leftTail
        have rightTail :
            (source, rightTarget) ∈
              SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
                (second :: rest) := by
          rcases rightEdge with rightFirst | rightTail
          · exact False.elim (firstSource rightFirst.1.symm)
          · exact rightTail
        exact adjacent_target_unique_of_count_one source
          (second :: rest) leftTarget rightTarget
          tailCount leftTail rightTail

/-- A unique passing supported value is the result of finite-list search. -/
theorem find?_eq_some_of_unique
    (predicate : Nat → Bool) (target : Nat)
    (passes : predicate target = true)
    (unique : ∀ candidate, predicate candidate = true → candidate = target) :
    ∀ support : List Nat,
      target ∈ support → support.find? predicate = some target
  | [], present => by
      simp at present
  | candidate :: rest, present => by
      by_cases candidatePasses : predicate candidate = true
      · have same := unique candidate candidatePasses
        subst candidate
        simp [List.find?, passes]
      · have candidateFails : predicate candidate = false := by
          cases outcome : predicate candidate with
          | false => rfl
          | true => exact False.elim (candidatePasses outcome)
        have tailPresent : target ∈ rest := by
          rcases (List.mem_cons.mp present) with same | tail
          · subst candidate
            exact False.elim (candidatePasses passes)
          · exact tail
        simpa [List.find?, candidateFails] using
          find?_eq_some_of_unique predicate target passes unique
            rest tailPresent

/-- A search with no passing value is genuinely empty. -/
theorem find?_eq_none_of_no_matches
    (predicate : Nat → Bool)
    (noMatches : ∀ candidate, predicate candidate ≠ true) :
    ∀ support : List Nat,
      support.find? predicate = none
  | [] => by
      simp [List.find?]
  | candidate :: rest => by
      have fails : predicate candidate = false := by
        cases outcome : predicate candidate with
        | false => rfl
        | true => exact False.elim (noMatches candidate outcome)
      simpa [List.find?, fails] using
        find?_eq_none_of_no_matches predicate noMatches rest

/-- A globally simple source's actual next input letter is exactly the
signature-selected successor. -/
theorem signatureSuccessor?_eq_actual
    (word : Word Nat) (before after : List Nat)
    (source target : Nat)
    (split : word.toList = before ++ source :: target :: after)
    (simple : word.toList.count source = 1) :
    signatureSuccessor? word (firstOccurrenceSequence word.toList) source =
      some target := by
  have different : source ≠ target := by
    intro equal
    subst target
    rw [split, List.count_append, List.count_cons_self,
      List.count_cons_self] at simple
    omega
  have edge : (source, target) ∈ word.adjacentPairs :=
    (SemigroupBasis.CoRoots.S5_107.mem_adjacentPairs_iff_exists_split
      source target word).mpr ⟨before, after, split⟩
  have supported : target ∈ firstOccurrenceSequence word.toList := by
    apply
      (SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank087.Seed.mem_firstOccurrenceSequence_iff
        target word.toList).mpr
    rw [split]
    simp
  unfold signatureSuccessor?
  apply find?_eq_some_of_unique
    (fun candidate =>
      decide
        (source ≠ candidate ∧ word.toList.count source = 1 ∧
          (source, candidate) ∈ word.adjacentPairs)) target
  · simp [different, simple, edge]
  · intro candidate candidatePasses
    have candidateEdge : (source, candidate) ∈ word.adjacentPairs := by
      have selected :
          source ≠ candidate ∧ word.toList.count source = 1 ∧
            (source, candidate) ∈ word.adjacentPairs := by
        simpa only [decide_eq_true_eq] using candidatePasses
      exact selected.2.2
    apply adjacent_target_unique_of_count_one source word.toList
      candidate target simple
    · rw [SemigroupBasis.CoRoots.S5_107.listAdjacentPairs_toList]
      exact candidateEdge
    · rw [SemigroupBasis.CoRoots.S5_107.listAdjacentPairs_toList]
      exact edge
  · exact supported

private theorem getLastD_append_cons
    (before : List Nat) (head fallback : Nat)
    (after : List Nat) :
    (before ++ head :: after).getLastD fallback =
      after.getLastD head := by
  induction before generalizing fallback with
  | nil =>
      simp only [List.nil_append, List.getLastD_cons]
  | cons letter rest inductionHypothesis =>
      simp only [List.cons_append, List.getLastD_cons]
      exact inductionHypothesis letter

private theorem final_eq_getLastD_of_split
    (word : Word Nat) (before after : List Nat)
    (source : Nat)
    (split : word.toList = before ++ source :: after) :
    word.final = after.getLastD source := by
  cases word with
  | mk head tail =>
      have final :=
        congrArg
          (fun letters : List Nat => letters.getLastD head)
          split
      simpa only [Word.toList, Word.final,
        List.getLastD_cons, getLastD_append_cons] using final

/-- A globally simple final input letter has no signature successor. -/
theorem signatureSuccessor?_eq_none_at_final
    (word : Word Nat) (before : List Nat) (source : Nat)
    (split : word.toList = before ++ [source])
    (simple : word.toList.count source = 1) :
    signatureSuccessor? word (firstOccurrenceSequence word.toList) source =
      none := by
  have final : word.final = source := by
    simpa using
      final_eq_getLastD_of_split word before [] source split
  have simpleFinal :
      SemigroupBasis.CoRoots.S5_107.SimpleFinal word source :=
    ⟨simple, final⟩
  have noSuccessor :=
    (SemigroupBasis.CoRoots.S5_402.simpleFinal_iff_noImmediateSuccessor
      word source).mp simpleFinal
  unfold signatureSuccessor?
  apply find?_eq_none_of_no_matches
  intro candidate passes
  have selected :
      source ≠ candidate ∧ word.toList.count source = 1 ∧
        (source, candidate) ∈ word.adjacentPairs := by
    simpa only [decide_eq_true_eq] using passes
  exact noSuccessor.2 candidate selected

/-- Decoration already owed by a preceding globally simple letter. -/
def pendingSeenSuccessor
    (seen : List Nat) (afterSimple : Bool) : List Nat → List Nat
  | [] => []
  | marker :: _ =>
      if afterSimple = true ∧ marker ∈ seen then
        [marker, marker]
      else
        []

@[simp] theorem pendingSeenSuccessor_false
    (seen remaining : List Nat) :
    pendingSeenSuccessor seen false remaining = [] := by
  cases remaining <;> simp [pendingSeenSuccessor]

/-- Fable's exact prefix cut: scanner support, complete first-order support,
the pending-simple bit and the unprocessed suffix are all related together.
The extra pending decoration is indispensable when an already-seen repeated
marker immediately follows a globally simple input letter. -/
theorem stableStreamingFold_eq_signature_state
    (word : Word Nat) :
    ∀ (remaining before scannerSeen signatureSeen : List Nat)
      (afterSimple : Bool),
      word.toList = before ++ remaining →
      (∀ letter,
        letter ∈ scannerSeen ↔
          letter ∈ before ∧ word.toList.count letter ≠ 1) →
      (∀ letter, letter ∈ signatureSeen ↔ letter ∈ before) →
      stableStreamingFold word.toList scannerSeen afterSimple remaining =
        pendingSeenSuccessor signatureSeen afterSimple remaining ++
          renderFirstOrderSignature word
            (firstOccurrenceSequence word.toList) signatureSeen
            (firstOccurrenceAfterPrefix signatureSeen remaining) := by
  intro remaining
  induction remaining with
  | nil =>
      intro before scannerSeen signatureSeen afterSimple _ _ _
      simp [stableStreamingFold, pendingSeenSuccessor,
        firstOccurrenceAfterPrefix, renderFirstOrderSignature]
  | cons letter rest inductionHypothesis =>
      intro before scannerSeen signatureSeen afterSimple split
        scannerInvariant signatureInvariant
      have advanced :
          word.toList = (before ++ [letter]) ++ rest := by
        simpa [List.append_assoc] using split
      by_cases simple : word.toList.count letter = 1
      · have beforeAbsent : letter ∉ before := by
          intro present
          have positive : 0 < before.count letter :=
            List.count_pos_iff.mpr present
          rw [split, List.count_append,
            List.count_cons_self] at simple
          omega
        have signatureAbsent : letter ∉ signatureSeen := by
          intro present
          exact beforeAbsent ((signatureInvariant letter).mp present)
        have scannerNext :
            ∀ candidate,
              candidate ∈ scannerSeen ↔
                candidate ∈ before ++ [letter] ∧
                  word.toList.count candidate ≠ 1 := by
          intro candidate
          rw [scannerInvariant candidate]
          by_cases same : candidate = letter
          · subst candidate
            simp [simple]
          · simp [same]
        have signatureNext :
            ∀ candidate,
              candidate ∈ letter :: signatureSeen ↔
                candidate ∈ before ++ [letter] := by
          intro candidate
          simp [signatureInvariant candidate, or_comm]
        have tail :=
          inductionHypothesis (before ++ [letter]) scannerSeen
            (letter :: signatureSeen) true advanced
            scannerNext signatureNext
        have required :
            (match
              signatureSuccessor? word
                (firstOccurrenceSequence word.toList) letter with
             | none => []
             | some marker =>
                 if marker ∈ signatureSeen then [marker, marker] else []) =
              pendingSeenSuccessor
                (letter :: signatureSeen) true rest := by
          cases rest with
          | nil =>
              have finalSplit :
                  word.toList = before ++ [letter] := by
                simpa using split
              rw [signatureSuccessor?_eq_none_at_final
                word before letter finalSplit simple]
              simp [pendingSeenSuccessor]
          | cons marker after =>
              have actual :=
                signatureSuccessor?_eq_actual word before after
                  letter marker split simple
              rw [actual]
              have different : marker ≠ letter := by
                intro same
                subst marker
                rw [split, List.count_append,
                  List.count_cons_self, List.count_cons_self] at simple
                omega
              by_cases present : marker ∈ signatureSeen
              · simp [pendingSeenSuccessor, present]
              · simp [pendingSeenSuccessor, present, different]
        have noOuterPending :
            pendingSeenSuccessor signatureSeen afterSimple
              (letter :: rest) = [] := by
          simp [pendingSeenSuccessor, signatureAbsent]
        rw [stableStreamingFold, if_pos simple,
          noOuterPending, List.nil_append,
          firstOccurrenceAfterPrefix, if_neg signatureAbsent,
          renderFirstOrderSignature, if_pos simple]
        dsimp only
        rw [← required] at tail
        simpa [List.append_assoc] using
          congrArg (fun output : List Nat => letter :: output) tail
      · have knownEquivalent :
            letter ∈ scannerSeen ↔ letter ∈ signatureSeen := by
          rw [scannerInvariant letter, signatureInvariant letter]
          simp [simple]
        have scannerAppended :
            ∀ candidate,
              candidate ∈ scannerSeen ++ [letter] ↔
                candidate ∈ before ++ [letter] ∧
                  word.toList.count candidate ≠ 1 := by
          intro candidate
          simp only [List.mem_append, List.mem_singleton]
          rw [scannerInvariant candidate]
          by_cases same : candidate = letter
          · subst candidate
            simp [simple]
          · simp [same]
        by_cases signatureKnown : letter ∈ signatureSeen
        · have scannerKnown : letter ∈ scannerSeen :=
            knownEquivalent.mpr signatureKnown
          have beforeKnown : letter ∈ before :=
            (signatureInvariant letter).mp signatureKnown
          have scannerUnchanged :
              ∀ candidate,
                candidate ∈ scannerSeen ↔
                  candidate ∈ before ++ [letter] ∧
                    word.toList.count candidate ≠ 1 := by
            intro candidate
            rw [scannerInvariant candidate]
            by_cases same : candidate = letter
            · subst candidate
              simp [beforeKnown, simple]
            · simp [same]
          have signatureUnchanged :
              ∀ candidate,
                candidate ∈ signatureSeen ↔
                  candidate ∈ before ++ [letter] := by
            intro candidate
            rw [signatureInvariant candidate]
            by_cases same : candidate = letter
            · subst candidate
              simp [beforeKnown]
            · simp [same]
          cases afterSimple with
          | false =>
              have tail :=
                inductionHypothesis (before ++ [letter])
                  scannerSeen signatureSeen false advanced
                  scannerUnchanged signatureUnchanged
              simp only [pendingSeenSuccessor_false,
                List.nil_append] at tail
              simpa [stableStreamingFold, simple, scannerKnown,
                firstOccurrenceAfterPrefix, signatureKnown,
                pendingSeenSuccessor] using tail
          | true =>
              have tail :=
                inductionHypothesis (before ++ [letter])
                  (scannerSeen ++ [letter]) signatureSeen false advanced
                  scannerAppended signatureUnchanged
              simp only [pendingSeenSuccessor_false,
                List.nil_append] at tail
              have appended := congrArg
                (fun output : List Nat => [letter, letter] ++ output)
                tail
              simpa [stableStreamingFold, simple, scannerKnown,
                firstOccurrenceAfterPrefix, signatureKnown,
                pendingSeenSuccessor, List.append_assoc] using appended
        · have scannerAbsent : letter ∉ scannerSeen := by
            intro present
            exact signatureKnown (knownEquivalent.mp present)
          have signatureNext :
              ∀ candidate,
                candidate ∈ letter :: signatureSeen ↔
                  candidate ∈ before ++ [letter] := by
            intro candidate
            simp [signatureInvariant candidate, or_comm]
          have tail :=
            inductionHypothesis (before ++ [letter])
              (scannerSeen ++ [letter]) (letter :: signatureSeen)
              false advanced scannerAppended signatureNext
          simp only [pendingSeenSuccessor_false,
            List.nil_append] at tail
          have appended := congrArg
            (fun output : List Nat => [letter, letter] ++ output)
            tail
          simpa [stableStreamingFold, simple, scannerAbsent,
            firstOccurrenceAfterPrefix, signatureKnown,
            renderFirstOrderSignature, pendingSeenSuccessor,
            List.append_assoc] using appended

/-- The prefix-generalized state invariant discharges the EXACT pure scanner
obligation identified in the earlier owner-boundary packet. -/
theorem stableScannerSignatureAgreement :
    StableScannerSignatureAgreement := by
  intro word
  have state :=
    stableStreamingFold_eq_signature_state
      word word.toList [] [] [] false
      (by simp)
      (by intro letter; simp)
      (by intro letter; simp)
  rw [firstOccurrenceAfterPrefix_nil] at state
  have rendered :
      stableStreamingFold word.toList [] false word.toList =
        exactFirstOrderSignatureCanonicalList word := by
    simpa [exactFirstOrderSignatureCanonicalList] using state
  exact
    (stableStreamingFold_eq_ownerCanonical word.toList).symm.trans
      rendered

/-- The exact unrestricted first-order-preserving lower-owner lift is now
proved; it is no longer a conditional premise. -/
theorem firstOccurrencePreservingSimpleSuccessorLift :
    FirstOccurrencePreservingSimpleSuccessorLift :=
  stableScannerAgreement_implies_ownerLift
    stableScannerSignatureAgreement

/-- Exact frozen five-law owner intersection after the genuine unrestricted
prefix-state completeness proof. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis :=
  intersectionBasis_of_simpleSuccessorLift
    firstOccurrencePreservingSimpleSuccessorLift

/-- Reusable certified rank-090 family seed with no remaining premises. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The staged rank-090 representative is proved unconditionally. -/
theorem s6_8281_representative_basis :
    BasisFor S6_8281.table.semigroup basis :=
  S6_8281.representative_basis_of_normalizer normalizer

/-- The opposite orientation retains the exact reversed frozen presentation. -/
theorem s6_8281_opposite_basis :
    BasisFor S6_8281.table.semigroup.opposite (reversedBasis basis) :=
  S6_8281.opposite_basis_of_normalizer normalizer

/-- Shared reviewed transport retains the exact displayed-law derivations and
the independent unrestricted validity implications for both factors. -/
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

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank090.Seed

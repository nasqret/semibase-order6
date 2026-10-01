import SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness
import SemigroupBasis.CoRoots.S5_870GapBlocks

/-!
# Hull 21.1 profile-count normalization

This module isolates the constructive part of Lee--Zhang Section 21.2 from
the uniqueness argument.  The renderer below is a literal function of the
completed phase profile and capped multiplicities.  Consequently, two words
with the same joint signature have the same rendered list.

The remaining statement is one-sided: derive each source list to that
renderer with the fourteen Proposition 21.1 laws.  The helper theorems below
provide the operations used by that sweep without passing through either
factor's standalone canonical word.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis
namespace CoRoots
namespace Order6Hull21_1ProfileCountNormalization

open SemigroupBasis.CoRoots.S5_831

abbrev HullListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.HullListDerives

/-! ## Constructive moves retained by the joint basis -/

/-- A phase gap whose letters have all appeared in the displayed prefix can
be replaced by one anchor occurrence while the original gap is moved to the
final debt block.  This is the exact sweep step supplied by Lemma 21.2. -/
theorem hullListDerivesMoveSeenGapToDebt
    (pre post seen middle gap : List Nat) (anchor : Nat)
    (gapNonempty : gap ≠ [])
    (oldLetters :
      ∀ letter, letter ∈ gap → letter ∈ anchor :: seen) :
    HullListDerives
      (pre ++ [anchor] ++ seen ++ gap ++ middle ++ [anchor] ++ post)
      (pre ++ [anchor] ++ seen ++ [anchor] ++ middle ++
        [anchor] ++ gap ++ post) :=
  SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.hullListDerivesRedistribute
    pre post seen middle gap anchor gapNonempty oldLetters

/-- Adjacent debt letters can be interchanged after a fixed prefix already
contains a witness for each letter. -/
theorem hullListDerivesSwapAfterWitnesses
    (witnesses suffix : List Nat) (x y : Nat)
    (xMember : x ∈ witnesses)
    (yMember : y ∈ witnesses) :
    HullListDerives
      (witnesses ++ [x, y] ++ suffix)
      (witnesses ++ [y, x] ++ suffix) := by
  by_cases equal : x = y
  · subst y
    exact
      SemigroupBasis.CoRoots.S5_107.ListDerives.refl
        (basis :=
          SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis)
        _
  · rcases List.append_of_mem xMember with
      ⟨beforeX, afterX, rfl⟩
    simp only [List.mem_append, List.mem_cons] at yMember
    rcases yMember with yBefore | yEqual | yAfter
    · rcases List.append_of_mem yBefore with
        ⟨beforeY, between, rfl⟩
      have swapped :=
        (SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.hullListDerivesExchange
          beforeY suffix between afterX [] y x).symm
      simpa [List.append_assoc] using swapped
    · exact False.elim (equal yEqual.symm)
    · rcases List.append_of_mem yAfter with
        ⟨between, afterY, rfl⟩
      have swapped :=
        SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.hullListDerivesExchange
          beforeX suffix between afterY [] x y
      simpa [List.append_assoc] using swapped

/-- Any permutation of a debt tail is derivable once every debt letter has
an earlier witness in the fixed prefix. -/
theorem hullListDerivesPermuteAfterWitnesses
    (witnesses suffix : List Nat)
    {source target : List Nat}
    (covered :
      ∀ letter, letter ∈ source → letter ∈ witnesses)
    (permutation : source.Perm target) :
    HullListDerives
      (witnesses ++ source ++ suffix)
      (witnesses ++ target ++ suffix) := by
  induction permutation generalizing witnesses suffix with
  | nil =>
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis :=
            SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis)
          _
  | cons head permutation induction =>
      have tailDerivation :=
        induction
          (witnesses ++ [head]) suffix
          (fun letter member =>
            List.mem_append.mpr <|
              Or.inl <|
                covered letter (List.Mem.tail head member))
      simpa [List.append_assoc] using tailDerivation
  | swap left right rest =>
      have leftMember : left ∈ witnesses :=
        covered left (by simp)
      have rightMember : right ∈ witnesses :=
        covered right (by simp)
      have swapped :=
        (hullListDerivesSwapAfterWitnesses
          witnesses (rest ++ suffix)
          left right leftMember rightMember).symm
      simpa [List.append_assoc] using swapped
  | trans first second firstInduction secondInduction =>
      have firstDerivation :=
        firstInduction witnesses suffix covered
      have secondDerivation :=
        secondInduction witnesses suffix
          (fun letter member =>
            covered letter ((first.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

/-- Once a witness has appeared, two adjacent later copies contract to one.
This is the list form used to cap each sorted final debt at one copy. -/
theorem hullListDerivesContractAfterWitness
    (witnesses suffix : List Nat) (letter : Nat)
    (member : letter ∈ witnesses) :
    HullListDerives
      (witnesses ++ [letter, letter] ++ suffix)
      (witnesses ++ [letter] ++ suffix) := by
  rcases List.append_of_mem member with
    ⟨before, after, rfl⟩
  simpa [List.append_assoc] using
    SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.hullListDerivesPowerContract
      before suffix after letter

/-! ## Support normalization behind existing witnesses -/

private def hullDeduplicateLater : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      if letter ∈ rest then
        hullDeduplicateLater rest
      else
        letter :: hullDeduplicateLater rest

private theorem hullDeduplicateLater_mem_iff (tested : Nat) :
    ∀ letters : List Nat,
      tested ∈ hullDeduplicateLater letters ↔ tested ∈ letters
  | [] => by simp [hullDeduplicateLater]
  | letter :: rest => by
      by_cases present : letter ∈ rest
      · rw [hullDeduplicateLater, if_pos present,
          hullDeduplicateLater_mem_iff tested rest]
        constructor
        · exact List.Mem.tail letter
        · intro member
          rcases List.mem_cons.mp member with atLetter | inRest
          · simpa [atLetter] using present
          · exact inRest
      · by_cases equal : tested = letter
        · subst tested
          simp [hullDeduplicateLater, present]
        · simp [hullDeduplicateLater, present, equal,
            hullDeduplicateLater_mem_iff tested rest]

private theorem hullDeduplicateLater_nodup :
    ∀ letters : List Nat,
      (hullDeduplicateLater letters).Nodup
  | [] => by simp [hullDeduplicateLater]
  | letter :: rest => by
      by_cases present : letter ∈ rest
      · simpa [hullDeduplicateLater, present] using
          hullDeduplicateLater_nodup rest
      · rw [hullDeduplicateLater, if_neg present,
          List.nodup_cons]
        exact
          ⟨by
            intro member
            exact present <|
              (hullDeduplicateLater_mem_iff letter rest).mp
                member,
            hullDeduplicateLater_nodup rest⟩

private theorem hullPermOfNodupMemIff
    {left right : List Nat}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (members :
      ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro letter
  rw [leftNodup.count, rightNodup.count]
  simp only [members letter]

private theorem hullListDerivesDeduplicateAfterWitnesses
    (suffix : List Nat) :
    ∀ (witnesses source : List Nat),
      (∀ letter, letter ∈ source → letter ∈ witnesses) →
      HullListDerives
        (witnesses ++ source ++ suffix)
        (witnesses ++ hullDeduplicateLater source ++ suffix)
  | _, [], _ => by
      simpa using
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis :=
            SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis)
          _
  | witnesses, letter :: rest, sourceWitnessed => by
      have restWitnessed :
          ∀ tested, tested ∈ rest →
            tested ∈ witnesses ++ [letter] := by
        intro tested member
        exact List.mem_append.mpr <| Or.inl <|
          sourceWitnessed tested (List.Mem.tail letter member)
      have recurse :=
        hullListDerivesDeduplicateAfterWitnesses
          suffix (witnesses ++ [letter]) rest restWitnessed
      have recurseShape :
          HullListDerives
            (witnesses ++ (letter :: rest) ++ suffix)
            (witnesses ++ [letter] ++
              hullDeduplicateLater rest ++ suffix) := by
        simpa [List.append_assoc] using recurse
      by_cases present : letter ∈ rest
      · have retained :
            letter ∈ hullDeduplicateLater rest :=
          (hullDeduplicateLater_mem_iff letter rest).mpr present
        have exposePermutation :
            (letter :: hullDeduplicateLater rest).Perm
              (letter :: letter ::
                (hullDeduplicateLater rest).erase letter) :=
          List.Perm.cons letter (List.perm_cons_erase retained)
        have exposeWitnessed :
            ∀ tested,
              tested ∈ letter :: hullDeduplicateLater rest →
                tested ∈ witnesses := by
          intro tested member
          rcases List.mem_cons.mp member with atLetter | inRest
          · simpa [atLetter] using
              sourceWitnessed letter (List.Mem.head rest)
          · exact sourceWitnessed tested
              (List.Mem.tail letter <|
                (hullDeduplicateLater_mem_iff tested rest).mp
                  inRest)
        have expose :
            HullListDerives
              (witnesses ++ [letter] ++
                hullDeduplicateLater rest ++ suffix)
              (witnesses ++ [letter, letter] ++
                (hullDeduplicateLater rest).erase letter ++
                suffix) := by
          simpa [List.append_assoc] using
            hullListDerivesPermuteAfterWitnesses
              witnesses suffix exposeWitnessed
              exposePermutation
        have contract :
            HullListDerives
              (witnesses ++ [letter, letter] ++
                (hullDeduplicateLater rest).erase letter ++
                suffix)
              (witnesses ++ [letter] ++
                (hullDeduplicateLater rest).erase letter ++
                suffix) := by
          simpa [List.append_assoc] using
            hullListDerivesContractAfterWitness
              witnesses
              ((hullDeduplicateLater rest).erase letter ++
                suffix)
              letter
              (sourceWitnessed letter (List.Mem.head rest))
        have restoreForward :=
          hullListDerivesPermuteAfterWitnesses
            witnesses suffix
            (by
              intro tested member
              exact sourceWitnessed tested
                (List.Mem.tail letter <|
                  (hullDeduplicateLater_mem_iff
                    tested rest).mp member))
            (List.perm_cons_erase retained)
        have restore :
            HullListDerives
              (witnesses ++ [letter] ++
                (hullDeduplicateLater rest).erase letter ++
                suffix)
              (witnesses ++ hullDeduplicateLater rest ++
                suffix) := by
          simpa [List.append_assoc] using restoreForward.symm
        rw [hullDeduplicateLater, if_pos present]
        simpa [List.append_assoc] using
          recurseShape.trans <|
            expose.trans (contract.trans restore)
      · rw [hullDeduplicateLater, if_neg present]
        simpa [List.append_assoc] using recurseShape

/-- Behind a prefix containing every displayed debt letter, multiplicity and
order are immaterial; only support remains. -/
theorem hullListDerivesOfSameSupportAfterWitnesses
    (witnesses suffix left right : List Nat)
    (leftWitnessed :
      ∀ letter, letter ∈ left → letter ∈ witnesses)
    (rightWitnessed :
      ∀ letter, letter ∈ right → letter ∈ witnesses)
    (sameSupport :
      ∀ letter, letter ∈ left ↔ letter ∈ right) :
    HullListDerives
      (witnesses ++ left ++ suffix)
      (witnesses ++ right ++ suffix) := by
  have leftReduction :=
    hullListDerivesDeduplicateAfterWitnesses
      suffix witnesses left leftWitnessed
  have rightReduction :=
    hullListDerivesDeduplicateAfterWitnesses
      suffix witnesses right rightWitnessed
  have reducedSupport :
      ∀ letter,
        letter ∈ hullDeduplicateLater left ↔
          letter ∈ hullDeduplicateLater right := by
    intro letter
    rw [hullDeduplicateLater_mem_iff,
      hullDeduplicateLater_mem_iff, sameSupport]
  have permutation :
      (hullDeduplicateLater left).Perm
        (hullDeduplicateLater right) :=
    hullPermOfNodupMemIff
      (hullDeduplicateLater_nodup left)
      (hullDeduplicateLater_nodup right)
      reducedSupport
  have reducedWitnessed :
      ∀ letter,
        letter ∈ hullDeduplicateLater left →
          letter ∈ witnesses := by
    intro letter member
    exact leftWitnessed letter <|
      (hullDeduplicateLater_mem_iff letter left).mp member
  exact leftReduction.trans <|
    (hullListDerivesPermuteAfterWitnesses
      witnesses suffix reducedWitnessed permutation).trans
      rightReduction.symm

/-! ## Deterministic profile-count renderer -/

/-- The capped multiplicity function retained from the `S3_8` factor. -/
def cappedCountProfile (letters : List Nat) : Nat → Nat :=
  fun letter => Nat.min (letters.count letter) 2

/-- Whether a phase label is globally repeated according to the capped
multiplicity profile. -/
def phaseRepeated
    (counts : Nat → Nat) (phase : Phase) : Bool :=
  decide (counts phase.label = 2)

private abbrev PhaseCoreSplit := List Phase × Phase × List Phase

/-- Split at the final doubled phase.  The third component is the literal
trailing run of undoubled phases. -/
private def splitLastDoubledPhase :
    List Phase → Option PhaseCoreSplit
  | [] => none
  | phase :: rest =>
      match splitLastDoubledPhase rest with
      | some (before, lastPhase, suffix) =>
          some (phase :: before, lastPhase, suffix)
      | none =>
          if phase.doubled then
            some ([], phase, rest)
          else
            none

/-- Render all core phases except the last.  A doubled phase retains one
copy of the first repeated label as its canonical old-letter witness. -/
def renderProfileCountCorePrefix
    (anchor : Nat) : List Phase → List Nat
  | [] => []
  | phase :: rest =>
      phase.label ::
        ((if phase.doubled then [anchor] else []) ++
          renderProfileCountCorePrefix anchor rest)

/-- Canonical rendering after the first repeated phase.

The core ends at the last doubled phase.  The final debt always starts with
the anchor and then contains one copy of every later globally repeated
label. -/
def renderProfileCountCore
    (counts : Nat → Nat)
    (anchorPhase : Phase) (rest : List Phase) : List Nat :=
  let phases := anchorPhase :: rest
  match splitLastDoubledPhase phases with
  | none => phaseLabels phases
  | some (before, lastPhase, suffix) =>
      let core := before ++ [lastPhase]
      let repeatedLater :=
        phaseLabels
          ((core.drop 1).filter (phaseRepeated counts))
      renderProfileCountCorePrefix anchorPhase.label before ++
        [lastPhase.label, anchorPhase.label] ++ repeatedLater ++
        phaseLabels suffix

/-- Canonical list determined only by a completed phase profile and a capped
count function.  If there is no repeated label, the phase labels themselves
are the original simple word. -/
def profileCountCanonicalListFrom
    (phases : List Phase) (counts : Nat → Nat) : List Nat :=
  let simplePrefix :=
    phases.takeWhile
      (fun phase => !(phaseRepeated counts phase))
  match
      phases.dropWhile
        (fun phase => !(phaseRepeated counts phase)) with
  | [] => phaseLabels phases
  | anchorPhase :: rest =>
      phaseLabels simplePrefix ++
        renderProfileCountCore counts anchorPhase rest

/-- The deterministic joint representative of a source list. -/
def profileCountCanonicalList (letters : List Nat) : List Nat :=
  profileCountCanonicalListFrom
    (phaseProfileList letters)
    (cappedCountProfile letters)

/-- Equal joint signatures give literally equal deterministic
representatives.  No derivational or one-factor normalization claim is used
here. -/
theorem profileCountCanonicalList_eq
    {left right : List Nat}
    (profile :
      phaseProfileList left = phaseProfileList right)
    (counts :
      ∀ letter : Nat,
        Nat.min (left.count letter) 2 =
          Nat.min (right.count letter) 2) :
    profileCountCanonicalList left =
      profileCountCanonicalList right := by
  have countProfiles :
      cappedCountProfile left =
        cappedCountProfile right := by
    funext letter
    exact counts letter
  unfold profileCountCanonicalList
  rw [profile, countProfiles]

/-! ## Executable phase-gap scaffold -/

/-- Convert an executable first-occurrence gap block into the corresponding
scanner phase.  A phase is doubled precisely when its old-letter gap is
nonempty. -/
def phaseOfGapBlock
    (block : SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock) : Phase where
  label := block.marker
  doubled := decide (block.seconds ≠ [])

/-- Whether a block marker is globally repeated according to the retained
capped-count profile. -/
def gapBlockRepeated
    (counts : Nat → Nat)
    (block : SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock) : Bool :=
  decide (counts block.marker = 2)

private abbrev GapCoreSplit :=
  List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock ×
    SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock ×
      List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock

/-- Split at the final block with a nonempty old-letter gap.  Returning
`none` means that every block has an empty gap. -/
private def splitLastNonemptyGap :
    List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock →
      Option GapCoreSplit
  | [] => none
  | block :: rest =>
      match splitLastNonemptyGap rest with
      | some (before, lastBlock, suffix) =>
          some (block :: before, lastBlock, suffix)
      | none =>
          if block.seconds = [] then
            none
          else
            some ([], block, rest)

/-- Render all nonfinal core blocks after redistribution.  Every nonempty
old-letter gap is replaced by one copy of the first repeated marker. -/
def renderSweptCorePrefix
    (anchor : Nat) :
    List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock → List Nat
  | [] => []
  | block :: rest =>
      block.marker ::
        ((if block.seconds = [] then [] else [anchor]) ++
          renderSweptCorePrefix anchor rest)

/-- The exact intermediate produced by the Lee--Zhang block sweep.

All old-letter gaps in the nonfinal core are accumulated in reverse block
order, preserving the order inside each individual gap.  The final core gap
then follows in its original order.  One additional anchor copy starts this
debt after the final core marker.  This is the exact order produced by the
forward redistribution induction; the debt is intentionally neither permuted
nor contracted here. -/
def renderSweptCore
    (anchorBlock : SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock)
    (rest : List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock) : List Nat :=
  let blocks := anchorBlock :: rest
  match splitLastNonemptyGap blocks with
  | none => SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks
  | some (before, lastBlock, suffix) =>
      renderSweptCorePrefix anchorBlock.marker before ++
        [lastBlock.marker, anchorBlock.marker] ++
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds before.reverse ++
        lastBlock.seconds ++
        SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffix

/-- Swept rendering of a parsed block list.  Blocks before the first globally
repeated marker form the literal simple prefix. -/
def profileCountSweptListFrom
    (blocks : List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock)
    (counts : Nat → Nat) : List Nat :=
  let simplePrefix :=
    blocks.takeWhile
      (fun block => !(gapBlockRepeated counts block))
  match
      blocks.dropWhile
        (fun block => !(gapBlockRepeated counts block)) with
  | [] => SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks
  | anchorBlock :: rest =>
      SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simplePrefix ++
        renderSweptCore anchorBlock rest

/-- Canonical target computed from parsed blocks rather than by rescanning
their rendering. -/
def profileCountBlockCanonicalList
    (blocks : List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock) : List Nat :=
  profileCountCanonicalListFrom
    (blocks.map phaseOfGapBlock)
    (cappedCountProfile (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks))

/-! ## Pure final-debt data -/

abbrev SweptGapBlock :=
  SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock

private abbrev GapBlock := SweptGapBlock

private theorem renderGapBlocks_append
    (left right : List GapBlock) :
    SemigroupBasis.CoRoots.S5_870.renderGapBlocks (left ++ right) =
      SemigroupBasis.CoRoots.S5_870.renderGapBlocks left ++
        SemigroupBasis.CoRoots.S5_870.renderGapBlocks right := by
  induction left with
  | nil =>
      rfl
  | cons block rest induction =>
      simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
        induction, List.append_assoc]

private theorem renderGapBlocks_eq_gapBlockMarkers_of_seconds_eq_nil
    (blocks : List GapBlock)
    (empty :
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks = []) :
    SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks =
      SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block rest induction =>
      cases secondsShape : block.seconds with
      | nil =>
          have restEmpty :
              SemigroupBasis.CoRoots.S5_870.gapBlockSeconds rest = [] := by
            simpa [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
              secondsShape] using empty
          simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
            SemigroupBasis.CoRoots.S5_870.gapBlockMarkers,
            secondsShape, induction restEmpty]
      | cons letter tail =>
          have impossible :
              letter ∈
                SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                  (block :: rest) := by
            simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
              secondsShape]
          rw [empty] at impossible
          simp at impossible

private theorem gapBlockMarker_mem_renderGapBlocks
    (letter : Nat) :
    ∀ {blocks : List GapBlock},
      letter ∈ SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks →
        letter ∈ SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks
  | [], member => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers] at member
  | block :: rest, member => by
      simp only [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers,
        List.map_cons, List.mem_cons] at member
      rcases member with atMarker | inRest
      · subst letter
        simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks]
      · simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
          gapBlockMarker_mem_renderGapBlocks letter inRest]

private theorem gapBlockSecond_mem_renderGapBlocks
    (letter : Nat) :
    ∀ {blocks : List GapBlock},
      letter ∈ SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks →
        letter ∈ SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks
  | [], member => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds] at member
  | block :: rest, member => by
      simp only [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
        List.flatMap_cons, List.mem_append] at member
      rcases member with inBlock | inRest
      · simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks, inBlock]
      · simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
          gapBlockSecond_mem_renderGapBlocks letter inRest]

@[simp]
private theorem phaseLabels_map_phaseOfGapBlock
    (blocks : List GapBlock) :
    phaseLabels (blocks.map phaseOfGapBlock) =
      SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block rest induction =>
      simp [phaseLabels, phaseOfGapBlock,
        SemigroupBasis.CoRoots.S5_870.gapBlockMarkers, induction]

@[simp]
private theorem phaseRepeated_phaseOfGapBlock
    (counts : Nat → Nat) (block : GapBlock) :
    phaseRepeated counts (phaseOfGapBlock block) =
      gapBlockRepeated counts block := by
  rfl

private theorem renderProfileCountCorePrefix_map_phaseOfGapBlock
    (anchor : Nat) :
    ∀ blocks : List GapBlock,
      renderProfileCountCorePrefix anchor
          (blocks.map phaseOfGapBlock) =
        renderSweptCorePrefix anchor blocks
  | [] => rfl
  | block :: rest => by
      by_cases empty : block.seconds = []
      · simp [renderProfileCountCorePrefix, renderSweptCorePrefix,
          phaseOfGapBlock, empty,
          renderProfileCountCorePrefix_map_phaseOfGapBlock anchor rest]
      · simp [renderProfileCountCorePrefix, renderSweptCorePrefix,
          phaseOfGapBlock, empty,
          renderProfileCountCorePrefix_map_phaseOfGapBlock anchor rest]

private theorem takeWhile_map_phaseOfGapBlock
    (counts : Nat → Nat) :
    ∀ blocks : List GapBlock,
      (blocks.map phaseOfGapBlock).takeWhile
          (fun phase => !(phaseRepeated counts phase)) =
        (blocks.takeWhile
          (fun block => !(gapBlockRepeated counts block))).map
            phaseOfGapBlock
  | [] => rfl
  | block :: rest => by
      cases repeated : gapBlockRepeated counts block <;>
        simp [phaseRepeated_phaseOfGapBlock, repeated,
          takeWhile_map_phaseOfGapBlock counts rest]

private theorem dropWhile_map_phaseOfGapBlock
    (counts : Nat → Nat) :
    ∀ blocks : List GapBlock,
      (blocks.map phaseOfGapBlock).dropWhile
          (fun phase => !(phaseRepeated counts phase)) =
        (blocks.dropWhile
          (fun block => !(gapBlockRepeated counts block))).map
            phaseOfGapBlock
  | [] => rfl
  | block :: rest => by
      cases repeated : gapBlockRepeated counts block <;>
        simp [phaseRepeated_phaseOfGapBlock, repeated,
          dropWhile_map_phaseOfGapBlock counts rest]

private def phaseCoreSplitOfGap :
    GapCoreSplit → PhaseCoreSplit
  | (before, lastBlock, suffix) =>
      (before.map phaseOfGapBlock, phaseOfGapBlock lastBlock,
        suffix.map phaseOfGapBlock)

private theorem splitLastDoubledPhase_map_phaseOfGapBlock :
    ∀ blocks : List GapBlock,
      splitLastDoubledPhase (blocks.map phaseOfGapBlock) =
        (splitLastNonemptyGap blocks).map phaseCoreSplitOfGap
  | [] => rfl
  | block :: rest => by
      simp only [List.map_cons, splitLastDoubledPhase,
        splitLastNonemptyGap]
      rw [splitLastDoubledPhase_map_phaseOfGapBlock rest]
      cases split : splitLastNonemptyGap rest with
      | none =>
          by_cases empty : block.seconds = []
          · simp [split, phaseOfGapBlock, empty, phaseCoreSplitOfGap]
          · simp [split, phaseOfGapBlock, empty, phaseCoreSplitOfGap]
      | some data =>
          rcases data with ⟨before, lastBlock, suffix⟩
          simp [split, phaseCoreSplitOfGap]

private theorem mem_gapBlockSeconds_iff_two_le_count
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks)
    (tested : Nat) :
    tested ∈ SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks ↔
      2 ≤
        (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks).count
          tested := by
  rw [SemigroupBasis.CoRoots.S5_870.count_renderGapBlocks]
  have markersNodup := formed.markersNodup
  have markerCountLe :
      (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks).count
          tested ≤ 1 := by
    rw [markersNodup.count]
    split <;> omega
  constructor
  · intro inSeconds
    have inMarkers :
        tested ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks :=
      (formed.secondsInSeenOrMarkers tested inSeconds).resolve_left
        (by simp)
    have markerCount :
        (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks).count
            tested = 1 := by
      rw [markersNodup.count]
      simp [inMarkers]
    have secondsPositive :
        0 <
          (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks).count
            tested :=
      List.count_pos_iff.mpr inSeconds
    rw [markerCount]
    omega
  · intro total
    have secondsPositive :
        0 <
          (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks).count
            tested := by
      omega
    exact List.count_pos_iff.mp secondsPositive

private def seenAfterGapBlocks
    (seen : List Nat) (blocks : List GapBlock) : List Nat :=
  (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks).reverse ++ seen

private theorem gapBlockSeconds_append_local
    (left right : List GapBlock) :
    SemigroupBasis.CoRoots.S5_870.gapBlockSeconds (left ++ right) =
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds left ++
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds right := by
  exact List.flatMap_append

private theorem gapBlocksWellFormed_append
    {seen : List Nat} {left right : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
        seen (left ++ right)) :
    SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed seen left ∧
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
        (seenAfterGapBlocks seen left) right := by
  induction left generalizing seen with
  | nil =>
      exact
        ⟨SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed.nil seen,
          by simpa [seenAfterGapBlocks] using formed⟩
  | cons block rest induction =>
      cases formed with
      | cons _ _ _ markerFresh secondsSeen tailFormed =>
          obtain ⟨restFormed, rightFormed⟩ := induction tailFormed
          refine
            ⟨SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed.cons
                seen block rest markerFresh secondsSeen restFormed,
              ?_⟩
          simpa [seenAfterGapBlocks,
            SemigroupBasis.CoRoots.S5_870.gapBlockMarkers,
            List.append_assoc] using rightFormed

private theorem mem_gapBlockSeconds_reverse
    (tested : Nat) :
    ∀ blocks : List GapBlock,
      tested ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks.reverse ↔
        tested ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks
  | [] => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds]
  | block :: rest => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
        List.flatMap_append, mem_gapBlockSeconds_reverse tested rest,
        or_comm]

private theorem mem_reversedBeforeLastSeconds_iff
    (tested : Nat) (before : List GapBlock) (lastBlock : GapBlock) :
    tested ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds before.reverse ++
          lastBlock.seconds ↔
      tested ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
          (before ++ [lastBlock]) := by
  simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
    List.flatMap_append, mem_gapBlockSeconds_reverse tested, or_comm]

private theorem filter_map_phaseOfGapBlock
    (counts : Nat → Nat) :
    ∀ blocks : List GapBlock,
      (blocks.map phaseOfGapBlock).filter
          (phaseRepeated counts) =
        (blocks.filter (gapBlockRepeated counts)).map phaseOfGapBlock
  | [] => rfl
  | block :: rest => by
      cases repeated : gapBlockRepeated counts block <;>
        simp [phaseRepeated_phaseOfGapBlock, repeated,
          filter_map_phaseOfGapBlock counts rest]

private def repeatedLaterGapMarkers
    (counts : Nat → Nat) (before : List GapBlock)
    (lastBlock : GapBlock) : List Nat :=
  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
    (((before ++ [lastBlock]).drop 1).filter
      (gapBlockRepeated counts))

private theorem repeatedLaterPhaseLabels_eq
    (counts : Nat → Nat) (before : List GapBlock)
    (lastBlock : GapBlock) :
    phaseLabels
        ((((before ++ [lastBlock]).map phaseOfGapBlock).drop 1).filter
          (phaseRepeated counts)) =
      repeatedLaterGapMarkers counts before lastBlock := by
  unfold repeatedLaterGapMarkers
  rw [← List.map_drop]
  rw [filter_map_phaseOfGapBlock]
  exact phaseLabels_map_phaseOfGapBlock _

private def LastNonemptyGapResultSpec
    (blocks : List GapBlock) : Option GapCoreSplit → Prop
  | none =>
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks = []
  | some (before, lastBlock, suffixBlocks) =>
      blocks = before ++ [lastBlock] ++ suffixBlocks ∧
        lastBlock.seconds ≠ [] ∧
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds suffixBlocks = []

private theorem splitLastNonemptyGap_spec :
    ∀ blocks : List GapBlock,
      LastNonemptyGapResultSpec blocks (splitLastNonemptyGap blocks)
  | [] => by
      rfl
  | block :: rest => by
      have tailSpec := splitLastNonemptyGap_spec rest
      simp only [splitLastNonemptyGap]
      cases split : splitLastNonemptyGap rest with
      | none =>
          rw [split] at tailSpec
          change
            SemigroupBasis.CoRoots.S5_870.gapBlockSeconds rest = []
              at tailSpec
          by_cases empty : block.seconds = []
          · simp only [if_pos empty, LastNonemptyGapResultSpec]
            simpa [
              SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
              empty
            ] using tailSpec
          · simp only [if_neg empty, LastNonemptyGapResultSpec]
            exact ⟨rfl, empty, tailSpec⟩
      | some splitData =>
          rcases splitData with ⟨before, lastBlock, suffixBlocks⟩
          rw [split] at tailSpec
          rcases tailSpec with
            ⟨tailShape, lastNonempty, suffixSecondsEmpty⟩
          simp [LastNonemptyGapResultSpec, tailShape, lastNonempty,
            suffixSecondsEmpty, List.append_assoc]

private theorem splitLastNonemptyGap_some_spec
    {blocks before suffixBlocks : List GapBlock}
    {lastBlock : GapBlock}
    (split :
      splitLastNonemptyGap blocks =
        some (before, lastBlock, suffixBlocks)) :
    blocks = before ++ [lastBlock] ++ suffixBlocks ∧
      lastBlock.seconds ≠ [] ∧
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds suffixBlocks = [] := by
  have spec := splitLastNonemptyGap_spec blocks
  rw [split] at spec
  exact spec

private theorem takeWhile_append_dropWhile_bool
    {alpha : Type} (predicate : alpha → Bool) :
    ∀ values : List alpha,
      values.takeWhile predicate ++ values.dropWhile predicate = values
  | [] => rfl
  | value :: rest => by
      cases checked : predicate value <;>
        simp [checked, takeWhile_append_dropWhile_bool predicate rest]

private theorem mem_takeWhile_bool
    {alpha : Type} {predicate : alpha → Bool}
    {tested : alpha} :
    ∀ {values : List alpha},
      tested ∈ values.takeWhile predicate →
        predicate tested = true
  | [], member => by
      simp at member
  | value :: rest, member => by
      cases checked : predicate value
      · simp [checked] at member
      · simp [checked] at member
        rcases member with equal | inRest
        · simpa [equal] using checked
        · exact mem_takeWhile_bool inRest

private theorem head_dropWhile_bool_false
    {alpha : Type} (predicate : alpha → Bool) :
    ∀ (values : List alpha) (head : alpha) (tail : List alpha),
      values.dropWhile predicate = head :: tail →
        predicate head = false
  | [], head, tail, shape => by
      simp at shape
  | value :: rest, head, tail, shape => by
      cases checked : predicate value
      · simp [checked] at shape
        rcases shape with ⟨equal, _⟩
        simpa [← equal] using checked
      · simp [checked] at shape
        exact head_dropWhile_bool_false predicate rest head tail shape

private theorem simpleMarker_not_mem_wholeSeconds
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks)
    {block : GapBlock}
    (simpleMember :
      block ∈
        blocks.takeWhile
          (fun tested =>
            !(gapBlockRepeated
              (cappedCountProfile
                (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks))
              tested))) :
    block.marker ∉
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks := by
  let counts :=
    cappedCountProfile
      (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)
  have notRepeated :=
    mem_takeWhile_bool
      (predicate :=
        fun tested => !(gapBlockRepeated counts tested))
      (tested := block) simpleMember
  have repeatedFalse :
      gapBlockRepeated counts block = false := by
    cases repeated : gapBlockRepeated counts block <;>
      simp [repeated] at notRepeated ⊢
  intro inSeconds
  have repeatedCount :=
    (mem_gapBlockSeconds_iff_two_le_count formed block.marker).mp
      inSeconds
  have capped :
      counts block.marker = 2 := by
    simpa only [counts, cappedCountProfile] using
      (Nat.min_eq_right repeatedCount)
  have repeatedTrue :
      gapBlockRepeated counts block = true := by
    simp [gapBlockRepeated, capped]
  rw [repeatedFalse] at repeatedTrue
  contradiction

private theorem simpleGapBlockSeconds_eq_nil
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks) :
    let counts :=
      cappedCountProfile
        (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)
    let simpleBlocks :=
      blocks.takeWhile
        (fun block => !(gapBlockRepeated counts block))
    SemigroupBasis.CoRoots.S5_870.gapBlockSeconds simpleBlocks = [] := by
  dsimp only
  let counts :=
    cappedCountProfile
      (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)
  let simpleBlocks :=
    blocks.takeWhile
      (fun block => !(gapBlockRepeated counts block))
  let activeBlocks :=
    blocks.dropWhile
      (fun block => !(gapBlockRepeated counts block))
  have reconstruction :
      simpleBlocks ++ activeBlocks = blocks := by
    exact takeWhile_append_dropWhile_bool
      (fun block => !(gapBlockRepeated counts block)) blocks
  have simpleFormed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed []
        simpleBlocks := by
    obtain ⟨simpleFormed, _⟩ :=
      gapBlocksWellFormed_append
        (left := simpleBlocks) (right := activeBlocks) <| by
          simpa [reconstruction] using formed
    exact simpleFormed
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro letter inSimpleSeconds
  have inSimpleMarkers :
      letter ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks :=
    (simpleFormed.secondsInSeenOrMarkers
      letter inSimpleSeconds).resolve_left (by simp)
  obtain ⟨block, blockMember, markerEq⟩ :=
    List.mem_map.mp inSimpleMarkers
  have inWholeSeconds :
      letter ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks := by
    rw [← reconstruction,
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
      List.flatMap_append]
    exact List.mem_append.mpr <| Or.inl inSimpleSeconds
  have forbidden :=
    simpleMarker_not_mem_wholeSeconds formed
      (block := block) (by simpa [simpleBlocks, counts] using blockMember)
  exact forbidden <| by
    simpa [markerEq] using inWholeSeconds

private theorem suffixMarkers_not_mem_coreSeconds
    {seen : List Nat} {core suffixBlocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
        seen (core ++ suffixBlocks)) :
    ∀ letter,
      letter ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks →
        letter ∉
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds core := by
  obtain ⟨coreFormed, suffixFormed⟩ :=
    gapBlocksWellFormed_append formed
  intro letter inSuffix inCoreSeconds
  have known :=
    coreFormed.secondsInSeenOrMarkers letter inCoreSeconds
  have inSeenAfter :
      letter ∈ seenAfterGapBlocks seen core := by
    rcases known with inSeen | inCoreMarkers
    · exact List.mem_append.mpr <| Or.inr inSeen
    · exact List.mem_append.mpr <| Or.inl <| by
        simpa using inCoreMarkers
  exact
    (suffixFormed.markersAvoidSeen letter inSeenAfter) inSuffix

private theorem gapBlockMarker_mem_renderSweptCorePrefix
    (anchor letter : Nat) :
    ∀ {blocks : List GapBlock},
      letter ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks →
        letter ∈ renderSweptCorePrefix anchor blocks
  | [], member => by
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers] at member
  | block :: rest, member => by
      simp only [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers,
        List.map_cons, List.mem_cons] at member
      rcases member with atMarker | inRest
      · subst letter
        simp [renderSweptCorePrefix]
      · by_cases empty : block.seconds = []
        · simp [renderSweptCorePrefix, empty,
            gapBlockMarker_mem_renderSweptCorePrefix anchor letter inRest]
        · simp [renderSweptCorePrefix, empty,
            gapBlockMarker_mem_renderSweptCorePrefix anchor letter inRest]

private def blockDebtWitnesses
    (simpleBlocks : List GapBlock) (anchorBlock : GapBlock)
    (before : List GapBlock) (lastBlock : GapBlock) : List Nat :=
  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
    renderSweptCorePrefix anchorBlock.marker before ++
    [lastBlock.marker]

private theorem anchorMarker_mem_coreMarkers
    (anchorBlock : GapBlock) (rest before : List GapBlock)
    (lastBlock : GapBlock) (suffixBlocks : List GapBlock)
    (shape :
      anchorBlock :: rest =
        before ++ [lastBlock] ++ suffixBlocks) :
    anchorBlock.marker ∈
      SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
        (before ++ [lastBlock]) := by
  cases before with
  | nil =>
      simp only [List.nil_append, List.singleton_append] at shape
      injection shape with blockEq _
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers, blockEq]
  | cons first tail =>
      simp only [List.cons_append] at shape
      injection shape with blockEq _
      simp [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers, blockEq]

private theorem coreMarker_mem_blockDebtWitnesses
    (simpleBlocks : List GapBlock) (anchorBlock : GapBlock)
    (before : List GapBlock) (lastBlock : GapBlock) (letter : Nat)
    (member :
      letter ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
          (before ++ [lastBlock])) :
    letter ∈
      blockDebtWitnesses simpleBlocks anchorBlock before lastBlock := by
  have inBeforeOrLast :
      letter ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers before ∨
        letter = lastBlock.marker := by
    simpa [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers] using member
  rcases inBeforeOrLast with inBefore | atLast
  · have rendered :=
      gapBlockMarker_mem_renderSweptCorePrefix
        anchorBlock.marker letter inBefore
    simp [blockDebtWitnesses, rendered]
  · subst letter
    simp [blockDebtWitnesses]

private theorem mem_of_mem_drop_one
    {alpha : Type} {tested : alpha} :
    ∀ {values : List alpha},
      tested ∈ values.drop 1 → tested ∈ values
  | [], member => by
      simp at member
  | head :: tail, member =>
      List.Mem.tail head member

private theorem repeatedLaterGapMarker_mem_coreMarkers
    (counts : Nat → Nat) (before : List GapBlock)
    (lastBlock : GapBlock) (letter : Nat)
    (member :
      letter ∈ repeatedLaterGapMarkers counts before lastBlock) :
    letter ∈
      SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
        (before ++ [lastBlock]) := by
  unfold repeatedLaterGapMarkers at member
  obtain ⟨block, filteredMember, rfl⟩ :=
    List.mem_map.mp member
  have inDropped :=
    (List.mem_filter.mp filteredMember).1
  exact List.mem_map.mpr
    ⟨block, mem_of_mem_drop_one inDropped, rfl⟩

private theorem activeCoreSeconds_eq_wholeSeconds
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks)
    (counts : Nat → Nat)
    (countsShape :
      counts =
        cappedCountProfile
          (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks))
    (anchorBlock : GapBlock) (rest before : List GapBlock)
    (lastBlock : GapBlock) (suffixBlocks : List GapBlock)
    (activeShape :
      blocks.dropWhile
          (fun block => !(gapBlockRepeated counts block)) =
        anchorBlock :: rest)
    (coreShape :
      splitLastNonemptyGap (anchorBlock :: rest) =
        some (before, lastBlock, suffixBlocks)) :
    SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
        (before ++ [lastBlock]) =
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks := by
  let simpleBlocks :=
    blocks.takeWhile
      (fun block => !(gapBlockRepeated counts block))
  have reconstruction :
      simpleBlocks ++ (anchorBlock :: rest) = blocks := by
    rw [← activeShape]
    exact takeWhile_append_dropWhile_bool
      (fun block => !(gapBlockRepeated counts block)) blocks
  obtain ⟨splitShape, _, suffixSecondsEmpty⟩ :=
    splitLastNonemptyGap_some_spec coreShape
  have simpleSecondsEmpty :
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds simpleBlocks = [] := by
    simpa only [simpleBlocks, countsShape] using
      (simpleGapBlockSeconds_eq_nil formed)
  have wholeShape :
      blocks =
        simpleBlocks ++ (before ++ [lastBlock]) ++ suffixBlocks := by
    rw [← reconstruction, splitShape]
    simp [List.append_assoc]
  have simpleFlatMapEmpty :
      simpleBlocks.flatMap
          SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock.seconds =
        [] := by
    simpa only [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds] using
      simpleSecondsEmpty
  have suffixFlatMapEmpty :
      suffixBlocks.flatMap
          SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock.seconds =
        [] := by
    simpa only [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds] using
      suffixSecondsEmpty
  rw [wholeShape]
  simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
    List.flatMap_append, simpleFlatMapEmpty, suffixFlatMapEmpty,
    List.append_assoc]

private theorem activeCore_startsWithAnchor
    (anchorBlock : GapBlock) (rest before : List GapBlock)
    (lastBlock : GapBlock) (suffixBlocks : List GapBlock)
    (shape :
      anchorBlock :: rest =
        before ++ [lastBlock] ++ suffixBlocks) :
    ∃ coreRest,
      before ++ [lastBlock] = anchorBlock :: coreRest := by
  cases before with
  | nil =>
      simp only [List.nil_append, List.singleton_append] at shape
      injection shape with blockEq _
      subst lastBlock
      exact ⟨[], rfl⟩
  | cons first tail =>
      simp only [List.cons_append] at shape
      injection shape with blockEq _
      subst first
      exact ⟨tail ++ [lastBlock], rfl⟩

/-- Away from the explicit leading anchor, the active debt and the retained
later repeated markers have exactly the same support. -/
private theorem activeCoreSeconds_iff_repeatedLater_of_ne_anchor
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks)
    (counts : Nat → Nat)
    (countsShape :
      counts =
        cappedCountProfile
          (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks))
    (anchorBlock : GapBlock) (rest before : List GapBlock)
    (lastBlock : GapBlock) (suffixBlocks : List GapBlock)
    (activeShape :
      blocks.dropWhile
          (fun block => !(gapBlockRepeated counts block)) =
        anchorBlock :: rest)
    (coreShape :
      splitLastNonemptyGap (anchorBlock :: rest) =
        some (before, lastBlock, suffixBlocks))
    {letter : Nat}
    (notAnchor : letter ≠ anchorBlock.marker) :
    letter ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
          (before ++ [lastBlock]) ↔
      letter ∈
        repeatedLaterGapMarkers counts before lastBlock := by
  let simpleBlocks :=
    blocks.takeWhile
      (fun block => !(gapBlockRepeated counts block))
  have reconstruction :
      simpleBlocks ++ (anchorBlock :: rest) = blocks := by
    rw [← activeShape]
    exact takeWhile_append_dropWhile_bool
      (fun block => !(gapBlockRepeated counts block)) blocks
  obtain ⟨splitShape, _, _⟩ :=
    splitLastNonemptyGap_some_spec coreShape
  obtain ⟨coreRest, coreStarts⟩ :=
    activeCore_startsWithAnchor anchorBlock rest before lastBlock
      suffixBlocks splitShape
  have coreSecondsEq :=
    activeCoreSeconds_eq_wholeSeconds formed counts countsShape
      anchorBlock rest before lastBlock suffixBlocks activeShape coreShape
  have countTwoIff :
      counts letter = 2 ↔
        letter ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks := by
    rw [countsShape,
      mem_gapBlockSeconds_iff_two_le_count formed]
    simp only [cappedCountProfile, Nat.min_def]
    split <;> omega
  have splitFormed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed []
        (simpleBlocks ++ (anchorBlock :: rest)) := by
    rw [reconstruction]
    exact formed
  obtain ⟨_, activeFormed⟩ :=
    gapBlocksWellFormed_append
      (left := simpleBlocks) (right := anchorBlock :: rest)
        splitFormed
  have coreAndSuffixFormed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
        (seenAfterGapBlocks [] simpleBlocks)
        ((before ++ [lastBlock]) ++ suffixBlocks) := by
    rw [← splitShape]
    exact activeFormed
  obtain ⟨coreFormed, _⟩ :=
    gapBlocksWellFormed_append
      (left := before ++ [lastBlock]) (right := suffixBlocks)
        coreAndSuffixFormed
  constructor
  · intro inCoreSeconds
    have inWholeSeconds :
        letter ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks := by
      rw [← coreSecondsEq]
      exact inCoreSeconds
    have countTwo : counts letter = 2 :=
      countTwoIff.mpr inWholeSeconds
    have inCoreMarkers :
        letter ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
            (before ++ [lastBlock]) := by
      rcases
          coreFormed.secondsInSeenOrMarkers letter inCoreSeconds with
        inSimpleSeen | inMarkers
      · have inSimpleMarkers :
            letter ∈
              SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                simpleBlocks := by
          simpa [seenAfterGapBlocks] using inSimpleSeen
        obtain ⟨simpleBlock, simpleMember, markerEq⟩ :=
          List.mem_map.mp inSimpleMarkers
        have canonicalSimpleMember :
            simpleBlock ∈
              blocks.takeWhile
                (fun tested =>
                  !(gapBlockRepeated
                    (cappedCountProfile
                      (SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                        blocks))
                    tested)) := by
          simpa [simpleBlocks, countsShape] using simpleMember
        exfalso
        exact
          (simpleMarker_not_mem_wholeSeconds formed
            canonicalSimpleMember) <| by
              simpa [markerEq] using inWholeSeconds
      · exact inMarkers
    have inLaterCoreMarkers :
        letter ∈
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers coreRest := by
      rw [coreStarts] at inCoreMarkers
      simpa [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers,
        notAnchor] using inCoreMarkers
    unfold repeatedLaterGapMarkers
    rw [coreStarts]
    change
      letter ∈
        SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
          (coreRest.filter (gapBlockRepeated counts))
    obtain ⟨block, blockMember, markerEq⟩ :=
      List.mem_map.mp inLaterCoreMarkers
    apply List.mem_map.mpr
    refine
      ⟨block, List.mem_filter.mpr ⟨blockMember, ?_⟩, markerEq⟩
    have blockCount : counts block.marker = 2 := by
      simpa [markerEq] using countTwo
    simp [gapBlockRepeated, blockCount]
  · intro inLater
    unfold repeatedLaterGapMarkers at inLater
    obtain ⟨block, filteredMember, markerEq⟩ :=
      List.mem_map.mp inLater
    have blockRepeated :=
      (List.mem_filter.mp filteredMember).2
    have blockCount : counts block.marker = 2 := by
      simpa [gapBlockRepeated] using blockRepeated
    have countTwo : counts letter = 2 := by
      simpa [markerEq] using blockCount
    have inWholeSeconds :=
      countTwoIff.mp countTwo
    rw [coreSecondsEq]
    exact inWholeSeconds

/-- Exact support equivalence of the two displayed debts follows from the
active-core membership fact; reversing nonfinal block order changes no
support. -/
private theorem activeDebt_sameSupport
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks)
    (counts : Nat → Nat)
    (countsShape :
      counts =
        cappedCountProfile
          (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks))
    (anchorBlock : GapBlock) (rest before : List GapBlock)
    (lastBlock : GapBlock) (suffixBlocks : List GapBlock)
    (activeShape :
      blocks.dropWhile
          (fun block => !(gapBlockRepeated counts block)) =
        anchorBlock :: rest)
    (coreShape :
      splitLastNonemptyGap (anchorBlock :: rest) =
        some (before, lastBlock, suffixBlocks)) :
    ∀ letter,
      letter ∈
          anchorBlock.marker ::
            (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                before.reverse ++
              lastBlock.seconds) ↔
          letter ∈
            anchorBlock.marker ::
              repeatedLaterGapMarkers counts before lastBlock := by
    intro letter
    by_cases atAnchor : letter = anchorBlock.marker
    · simp [atAnchor]
    · simp only [List.mem_cons, atAnchor, false_or,
        mem_reversedBeforeLastSeconds_iff]
      exact
        activeCoreSeconds_iff_repeatedLater_of_ne_anchor
          formed counts countsShape anchorBlock rest before lastBlock
            suffixBlocks activeShape coreShape atAnchor

/-- The sole nondefinitional pure-list obligation after the renderer
simplification.  The hypotheses describe the active first-repeated branch and
the final nonempty-gap split exactly. -/
private theorem activeFinalDebtFacts
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks)
    (counts : Nat → Nat)
    (countsShape :
      counts =
        cappedCountProfile
          (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks))
    (anchorBlock : GapBlock) (rest before : List GapBlock)
    (lastBlock : GapBlock) (suffixBlocks : List GapBlock)
    (activeShape :
      blocks.dropWhile
          (fun block => !(gapBlockRepeated counts block)) =
        anchorBlock :: rest)
    (coreShape :
      splitLastNonemptyGap (anchorBlock :: rest) =
        some (before, lastBlock, suffixBlocks)) :
    let simpleBlocks :=
      blocks.takeWhile
        (fun block => !(gapBlockRepeated counts block))
    let witnesses :=
      blockDebtWitnesses simpleBlocks anchorBlock before lastBlock
    let sourceDebt :=
      anchorBlock.marker ::
        (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds before.reverse ++
          lastBlock.seconds)
    let targetDebt :=
      anchorBlock.marker ::
        repeatedLaterGapMarkers counts before lastBlock
    (∀ letter, letter ∈ sourceDebt → letter ∈ witnesses) ∧
      (∀ letter, letter ∈ targetDebt → letter ∈ witnesses) ∧
        ∀ letter, letter ∈ sourceDebt ↔ letter ∈ targetDebt := by
  dsimp only
  obtain ⟨splitShape, _, _⟩ :=
    splitLastNonemptyGap_some_spec coreShape
  have sameSupport :=
    activeDebt_sameSupport formed counts countsShape anchorBlock rest
      before lastBlock suffixBlocks activeShape coreShape
  have anchorInCore :=
    anchorMarker_mem_coreMarkers anchorBlock rest before lastBlock
      suffixBlocks splitShape
  have anchorWitnessed :=
    coreMarker_mem_blockDebtWitnesses
      (blocks.takeWhile
        (fun block => !(gapBlockRepeated counts block)))
      anchorBlock before lastBlock anchorBlock.marker anchorInCore
  have targetWitnessed :
      ∀ letter,
        letter ∈
            anchorBlock.marker ::
              repeatedLaterGapMarkers counts before lastBlock →
          letter ∈
            blockDebtWitnesses
              (blocks.takeWhile
                (fun block => !(gapBlockRepeated counts block)))
              anchorBlock before lastBlock := by
    intro letter member
    rcases List.mem_cons.mp member with atAnchor | inLater
    · subst letter
      exact anchorWitnessed
    · exact
        coreMarker_mem_blockDebtWitnesses
          (blocks.takeWhile
            (fun block => !(gapBlockRepeated counts block)))
          anchorBlock before lastBlock letter
          (repeatedLaterGapMarker_mem_coreMarkers
            counts before lastBlock letter inLater)
  refine ⟨?_, targetWitnessed, sameSupport⟩
  intro letter sourceMember
  exact targetWitnessed letter ((sameSupport letter).mp sourceMember)

/-- Public structural elimination interface for the block redistribution
stage.

The `same` branch records literal equality of the parsed source and swept
target.  The `active` branch exposes the first repeated marker, the final
nonempty gap, and the exact two renderer shapes.  It deliberately contains
only parser equations, well-formedness, and membership facts: consumers may
feed `finalDebtWitnessed` and `boundaryAnchorAvailable` directly to the
boundary-anchor API, while `historicalCoverage` discharges the historical
letter premise of the forward-sweep readiness API.

`beforeFinal` may be empty.  In that case `anchorPosition` identifies
`lastBlock` with `anchorBlock`; otherwise it exposes the remaining blocks
preceding the final nonempty gap.  Thus no consumer needs access to the
private `splitLastNonemptyGap` implementation. -/
inductive SweptCoreView (blocks : List SweptGapBlock) : Prop
  | same
      (sourceTargetShape :
        SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks =
          profileCountSweptListFrom blocks
            (cappedCountProfile
              (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks))) :
      SweptCoreView blocks
  | active
      (simpleBlocks : List SweptGapBlock)
      (anchorBlock : SweptGapBlock)
      (beforeFinal : List SweptGapBlock)
      (lastBlock : SweptGapBlock)
      (suffixBlocks : List SweptGapBlock)
      (blocksShape :
        blocks =
          simpleBlocks ++ beforeFinal ++ [lastBlock] ++ suffixBlocks)
      (anchorPosition :
        (beforeFinal = [] ∧ lastBlock = anchorBlock) ∨
          ∃ remainingBeforeFinal,
            beforeFinal = anchorBlock :: remainingBeforeFinal)
      (simpleWellFormed :
        SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
          [] simpleBlocks)
      (activeWellFormed :
        SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
          (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
            simpleBlocks).reverse
          (beforeFinal ++ [lastBlock] ++ suffixBlocks))
      (simpleSecondsEmpty :
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds simpleBlocks = [])
      (lastNonempty : lastBlock.seconds ≠ [])
      (suffixSecondsEmpty :
        SemigroupBasis.CoRoots.S5_870.gapBlockSeconds suffixBlocks = [])
      (sourceShape :
        SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks =
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
            SemigroupBasis.CoRoots.S5_870.renderGapBlocks beforeFinal ++
            [lastBlock.marker] ++ lastBlock.seconds ++
            SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
      (targetShape :
        profileCountSweptListFrom blocks
            (cappedCountProfile
              (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)) =
          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
            renderSweptCorePrefix anchorBlock.marker beforeFinal ++
            [lastBlock.marker, anchorBlock.marker] ++
            SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
              beforeFinal.reverse ++
            lastBlock.seconds ++
            SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
      (finalDebtWitnessed :
        ∀ letter, letter ∈ lastBlock.seconds →
          letter ∈
            SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks beforeFinal ++
              [lastBlock.marker])
      (boundaryAnchorAvailable :
        anchorBlock.marker ∈ lastBlock.seconds ∨
          ∃ before between after,
            SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                SemigroupBasis.CoRoots.S5_870.renderGapBlocks beforeFinal ++
                [lastBlock.marker] =
              before ++ [anchorBlock.marker] ++ between ++
                [anchorBlock.marker] ++ after)
      (historicalCoverage :
        ∀ letter,
          letter ∈
              anchorBlock.marker ::
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                  simpleBlocks).reverse →
            letter ∈
              SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                (beforeFinal ++ [lastBlock] ++ suffixBlocks) →
              letter = anchorBlock.marker) :
      SweptCoreView blocks

/-- Eliminate a well-formed parsed word into the public structural view used
by the Hull 21.1 block redistribution proof. -/
theorem sweptCoreView
    {blocks : List SweptGapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks) :
    SweptCoreView blocks := by
  classical
  let counts :=
    cappedCountProfile
      (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)
  let simpleBlocks :=
    blocks.takeWhile
      (fun block => !(gapBlockRepeated counts block))
  let activeBlocks :=
    blocks.dropWhile
      (fun block => !(gapBlockRepeated counts block))
  have reconstruction :
      simpleBlocks ++ activeBlocks = blocks := by
    exact takeWhile_append_dropWhile_bool
      (fun block => !(gapBlockRepeated counts block)) blocks
  have simpleSecondsEmpty :
      SemigroupBasis.CoRoots.S5_870.gapBlockSeconds simpleBlocks = [] := by
    simpa only [simpleBlocks, counts] using
      (simpleGapBlockSeconds_eq_nil formed)
  cases activeShape : activeBlocks with
  | nil =>
      have simpleBlocksEq : simpleBlocks = blocks := by
        rw [activeShape] at reconstruction
        simpa using reconstruction
      have wholeSecondsEmpty :
          SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks = [] := by
        rw [← simpleBlocksEq]
        exact simpleSecondsEmpty
      apply SweptCoreView.same
      calc
        SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks =
            SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks :=
          renderGapBlocks_eq_gapBlockMarkers_of_seconds_eq_nil
            blocks wholeSecondsEmpty
        _ =
            profileCountSweptListFrom blocks
              (cappedCountProfile
                (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)) := by
          symm
          simp [profileCountSweptListFrom, counts, activeBlocks,
            activeShape]
  | cons anchorBlock activeRest =>
      have activeShape' :
          blocks.dropWhile
              (fun block => !(gapBlockRepeated counts block)) =
            anchorBlock :: activeRest := by
        simpa [activeBlocks] using activeShape
      have reconstruction' :
          simpleBlocks ++ (anchorBlock :: activeRest) = blocks := by
        simpa [activeShape] using reconstruction
      obtain ⟨simpleWellFormed, activeWellFormed'⟩ :=
        gapBlocksWellFormed_append
          (left := simpleBlocks) (right := anchorBlock :: activeRest) <| by
            simpa [reconstruction'] using formed
      have activeWellFormed :
          SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
            (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
              simpleBlocks).reverse
            (anchorBlock :: activeRest) := by
        simpa [seenAfterGapBlocks] using activeWellFormed'
      cases coreShape :
          splitLastNonemptyGap (anchorBlock :: activeRest) with
      | none =>
          have activeSecondsEmpty :
              SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                (anchorBlock :: activeRest) = [] := by
            have splitSpec :=
              splitLastNonemptyGap_spec (anchorBlock :: activeRest)
            rw [coreShape] at splitSpec
            exact splitSpec
          have wholeSecondsEmpty :
              SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks = [] := by
            rw [← reconstruction']
            rw [gapBlockSeconds_append_local, simpleSecondsEmpty,
              activeSecondsEmpty]
            rfl
          have markerReconstruction :
              SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    (anchorBlock :: activeRest) =
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks := by
            simpa [SemigroupBasis.CoRoots.S5_870.gapBlockMarkers] using
              congrArg
                (List.map
                  SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock.marker)
                reconstruction'
          apply SweptCoreView.same
          calc
            SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks =
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers blocks :=
              renderGapBlocks_eq_gapBlockMarkers_of_seconds_eq_nil
                blocks wholeSecondsEmpty
            _ =
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers simpleBlocks ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    (anchorBlock :: activeRest) :=
              markerReconstruction.symm
            _ =
                profileCountSweptListFrom blocks
                  (cappedCountProfile
                    (SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                      blocks)) := by
              symm
              simp [profileCountSweptListFrom, counts, simpleBlocks,
                activeShape',
                renderSweptCore, coreShape]
      | some splitData =>
          rcases splitData with
            ⟨beforeFinal, lastBlock, suffixBlocks⟩
          obtain
            ⟨coreBlocksShape, lastNonempty, suffixSecondsEmpty⟩ :=
              splitLastNonemptyGap_some_spec coreShape
          have blocksShape :
              blocks =
                simpleBlocks ++ beforeFinal ++ [lastBlock] ++
                  suffixBlocks := by
            rw [← reconstruction', coreBlocksShape]
            simp [List.append_assoc]
          have activeWellFormed'' :
              SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed
                (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                  simpleBlocks).reverse
                (beforeFinal ++ [lastBlock] ++ suffixBlocks) := by
            simpa [coreBlocksShape] using activeWellFormed
          have anchorPosition :
              (beforeFinal = [] ∧ lastBlock = anchorBlock) ∨
                ∃ remainingBeforeFinal,
                  beforeFinal = anchorBlock :: remainingBeforeFinal := by
            cases beforeFinal with
            | nil =>
                simp only [List.nil_append, List.singleton_append]
                  at coreBlocksShape
                injection coreBlocksShape with blockEq _
                exact Or.inl ⟨rfl, blockEq.symm⟩
            | cons first remainingBeforeFinal =>
                simp only [List.cons_append] at coreBlocksShape
                injection coreBlocksShape with blockEq _
                subst first
                exact Or.inr ⟨remainingBeforeFinal, rfl⟩
          have simpleRender :
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks simpleBlocks =
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                  simpleBlocks :=
            renderGapBlocks_eq_gapBlockMarkers_of_seconds_eq_nil
              simpleBlocks simpleSecondsEmpty
          have suffixRender :
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks suffixBlocks =
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                  suffixBlocks :=
            renderGapBlocks_eq_gapBlockMarkers_of_seconds_eq_nil
              suffixBlocks suffixSecondsEmpty
          have sourceShape :
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks =
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    simpleBlocks ++
                  SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                    beforeFinal ++
                  [lastBlock.marker] ++ lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks := by
            rw [blocksShape]
            simp [renderGapBlocks_append,
              SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
              simpleRender, suffixRender, List.append_assoc]
          have targetShape :
              profileCountSweptListFrom blocks
                  (cappedCountProfile
                    (SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                      blocks)) =
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    simpleBlocks ++
                  renderSweptCorePrefix anchorBlock.marker beforeFinal ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                    beforeFinal.reverse ++
                  lastBlock.seconds ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks := by
            simp [profileCountSweptListFrom, counts, activeShape',
              renderSweptCore, coreShape, simpleBlocks,
              List.append_assoc]
          have historicalCoverage :
              ∀ letter,
                letter ∈
                    anchorBlock.marker ::
                      (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                        simpleBlocks).reverse →
                  letter ∈
                    SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                      (beforeFinal ++ [lastBlock] ++ suffixBlocks) →
                    letter = anchorBlock.marker := by
            intro letter inHistory inActiveSeconds
            rcases List.mem_cons.mp inHistory with atAnchor | inSimple
            · exact atAnchor
            · have inSimpleMarkers :
                  letter ∈
                    SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                      simpleBlocks := by
                simpa using inSimple
              obtain ⟨block, blockMember, markerEq⟩ :=
                List.mem_map.mp inSimpleMarkers
              have canonicalMember :
                  block ∈
                    blocks.takeWhile
                      (fun tested =>
                        !(gapBlockRepeated
                          (cappedCountProfile
                            (SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                              blocks))
                          tested)) := by
                simpa [simpleBlocks, counts] using blockMember
              have inWholeSeconds :
                  letter ∈
                    SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                      blocks := by
                have blocksShape' :
                    blocks =
                      simpleBlocks ++
                        (beforeFinal ++ [lastBlock] ++ suffixBlocks) := by
                  simpa [List.append_assoc] using blocksShape
                rw [blocksShape', gapBlockSeconds_append_local]
                exact List.mem_append.mpr <| Or.inr inActiveSeconds
              have forbidden :=
                simpleMarker_not_mem_wholeSeconds formed canonicalMember
              exact False.elim <| forbidden <| by
                simpa [markerEq] using inWholeSeconds
          obtain ⟨_, lastAndSuffixWellFormed⟩ :=
            gapBlocksWellFormed_append
              (left := beforeFinal)
              (right := lastBlock :: suffixBlocks) <| by
                simpa using activeWellFormed''
          have finalDebtWitnessed :
              ∀ letter, letter ∈ lastBlock.seconds →
                letter ∈
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                      simpleBlocks ++
                    SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                      beforeFinal ++
                    [lastBlock.marker] := by
            intro letter inDebt
            cases lastAndSuffixWellFormed with
            | cons historical _ _ _ secondsSeen _ =>
                have seen := secondsSeen letter inDebt
                rcases List.mem_cons.mp seen with atLast | inHistorical
                · subst letter
                  simp
                · have inBeforeOrSimple :
                      letter ∈
                          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                            beforeFinal ∨
                        letter ∈
                          SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                            simpleBlocks := by
                    simpa [seenAfterGapBlocks] using inHistorical
                  rcases inBeforeOrSimple with inBefore | inSimple
                  · have inRendered :=
                      gapBlockMarker_mem_renderGapBlocks
                        letter inBefore
                    simp [inRendered]
                  · simp [inSimple]
          have activeSecondsEq :
              SemigroupBasis.CoRoots.S5_870.gapBlockSeconds blocks =
                SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                  (beforeFinal ++ [lastBlock] ++ suffixBlocks) := by
            have blocksShape' :
                blocks =
                  simpleBlocks ++
                    (beforeFinal ++ [lastBlock] ++ suffixBlocks) := by
              simpa [List.append_assoc] using blocksShape
            rw [blocksShape', gapBlockSeconds_append_local,
              simpleSecondsEmpty]
            rfl
          have anchorPredicateFalse :=
            head_dropWhile_bool_false
              (fun block => !(gapBlockRepeated counts block))
              blocks anchorBlock activeRest activeShape'
          have anchorRepeated :
              gapBlockRepeated counts anchorBlock = true := by
            cases repeated : gapBlockRepeated counts anchorBlock <;>
              simp [repeated] at anchorPredicateFalse ⊢
          have anchorCount :
              counts anchorBlock.marker = 2 := by
            simpa [gapBlockRepeated] using anchorRepeated
          have anchorTotalCount :
              2 ≤
                (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks).count
                  anchorBlock.marker := by
            have capped :
                Nat.min
                    ((SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                      blocks).count anchorBlock.marker)
                    2 =
                  2 := by
              simpa [counts, cappedCountProfile] using anchorCount
            by_cases large :
                2 ≤
                  (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks).count
                    anchorBlock.marker
            · exact large
            · have countSmall :
                  (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks).count
                      anchorBlock.marker <
                    2 :=
                Nat.lt_of_not_ge large
              have minEq :
                  Nat.min
                      ((SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                        blocks).count anchorBlock.marker)
                      2 =
                    (SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                      blocks).count anchorBlock.marker :=
                Nat.min_eq_left (Nat.le_of_lt countSmall)
              rw [minEq] at capped
              omega
          have anchorInActiveSeconds :
              anchorBlock.marker ∈
                SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                  (beforeFinal ++ [lastBlock] ++ suffixBlocks) := by
            have inWhole :=
              (mem_gapBlockSeconds_iff_two_le_count
                formed anchorBlock.marker).mpr anchorTotalCount
            rw [activeSecondsEq] at inWhole
            exact inWhole
          have anchorInCoreDebt :
              anchorBlock.marker ∈
                  SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                    beforeFinal ++
                lastBlock.seconds := by
            rw [List.append_assoc] at anchorInActiveSeconds
            rw [gapBlockSeconds_append_local beforeFinal
                  ([lastBlock] ++ suffixBlocks),
                gapBlockSeconds_append_local [lastBlock] suffixBlocks,
                suffixSecondsEmpty] at anchorInActiveSeconds
            simpa [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
              List.append_assoc] using anchorInActiveSeconds
          have boundaryAnchorAvailable :
              anchorBlock.marker ∈ lastBlock.seconds ∨
                ∃ before between after,
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                        simpleBlocks ++
                      SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                        beforeFinal ++
                      [lastBlock.marker] =
                    before ++ [anchorBlock.marker] ++ between ++
                      [anchorBlock.marker] ++ after := by
            rcases List.mem_append.mp anchorInCoreDebt with
              inBeforeDebt | inLastDebt
            · rcases anchorPosition with
                ⟨beforeEmpty, _⟩ |
                  ⟨remainingBeforeFinal, beforeShape⟩
              · subst beforeFinal
                simp [SemigroupBasis.CoRoots.S5_870.gapBlockSeconds]
                  at inBeforeDebt
              · have afterFirstMember :
                    anchorBlock.marker ∈
                      anchorBlock.seconds ++
                        SemigroupBasis.CoRoots.S5_870.renderGapBlocks
                          remainingBeforeFinal := by
                  rw [beforeShape,
                    SemigroupBasis.CoRoots.S5_870.gapBlockSeconds,
                    List.flatMap_cons] at inBeforeDebt
                  rcases List.mem_append.mp inBeforeDebt with
                    inAnchorGap | inRemainingGaps
                  · exact List.mem_append.mpr <| Or.inl inAnchorGap
                  · exact List.mem_append.mpr <| Or.inr <|
                      gapBlockSecond_mem_renderGapBlocks
                        anchorBlock.marker inRemainingGaps
                obtain ⟨between, after, afterShape⟩ :=
                  List.append_of_mem afterFirstMember
                exact Or.inr
                  ⟨SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                      simpleBlocks,
                    between,
                    after ++ [lastBlock.marker],
                    by
                      rw [beforeShape]
                      simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks,
                        afterShape, List.append_assoc]⟩
            · exact Or.inl inLastDebt
          exact
            SweptCoreView.active
              simpleBlocks anchorBlock beforeFinal lastBlock suffixBlocks
              blocksShape anchorPosition simpleWellFormed
              activeWellFormed'' simpleSecondsEmpty lastNonempty
              suffixSecondsEmpty sourceShape targetShape
              finalDebtWitnessed boundaryAnchorAvailable
              historicalCoverage

/-- Exact pure-list interface required by final-debt normalization.

The active constructor records the common literal stem and suffix exposed by
the two renderers.  The swept debt is the anchor followed by all accumulated
second occurrences; the canonical debt is the anchor followed by the later
globally repeated phase labels. -/
private inductive BlockFinalDebtData :
    List Nat → List Nat → Prop
  | same {source target : List Nat}
      (shape : source = target) :
      BlockFinalDebtData source target
  | active {source target : List Nat}
      (witnesses suffix : List Nat)
      (anchor : Nat) (before : List GapBlock) (lastBlock : GapBlock)
      (repeatedLater : List Nat)
      (sourceShape :
        source =
          witnesses ++
            (anchor ::
              (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                  before.reverse ++
                lastBlock.seconds)) ++
            suffix)
      (targetShape :
        target =
          witnesses ++ (anchor :: repeatedLater) ++ suffix)
      (sourceWitnessed :
        ∀ letter,
          letter ∈
              anchor ::
                (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                    before.reverse ++
                  lastBlock.seconds) →
            letter ∈ witnesses)
      (targetWitnessed :
        ∀ letter, letter ∈ anchor :: repeatedLater →
          letter ∈ witnesses)
      (sameSupport :
        ∀ letter,
          letter ∈
              anchor ::
                (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                    before.reverse ++
                  lastBlock.seconds) ↔
            letter ∈ anchor :: repeatedLater) :
      BlockFinalDebtData source target

/-- The two simplified renderers expose either the same marker list or one
common stem followed by witnessed debts with equal support. -/
private theorem blockFinalDebtData
    {blocks : List GapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks)
    (nonempty : blocks ≠ []) :
    BlockFinalDebtData
      (profileCountSweptListFrom blocks
        (cappedCountProfile
          (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)))
      (profileCountBlockCanonicalList blocks) := by
  classical
  let counts :=
    cappedCountProfile
      (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)
  let activeBlocks :=
    blocks.dropWhile
      (fun block => !(gapBlockRepeated counts block))
  cases activeShape : activeBlocks with
  | nil =>
      apply BlockFinalDebtData.same
      simp [profileCountSweptListFrom, profileCountBlockCanonicalList,
        profileCountCanonicalListFrom, counts, activeBlocks, activeShape,
        takeWhile_map_phaseOfGapBlock,
        dropWhile_map_phaseOfGapBlock]
  | cons anchorBlock rest =>
      have activeShape' :
          blocks.dropWhile
              (fun block => !(gapBlockRepeated counts block)) =
            anchorBlock :: rest := by
        simpa [activeBlocks] using activeShape
      cases coreShape :
          splitLastNonemptyGap (anchorBlock :: rest) with
      | none =>
          have phaseCoreShape :
              splitLastDoubledPhase
                  ((anchorBlock :: rest).map phaseOfGapBlock) =
                none := by
            rw [splitLastDoubledPhase_map_phaseOfGapBlock, coreShape]
            rfl
          have phaseCoreShape' :
              splitLastDoubledPhase
                  (phaseOfGapBlock anchorBlock ::
                    rest.map phaseOfGapBlock) =
                none := by
            simpa only [List.map_cons] using phaseCoreShape
          have activeLabels :
              phaseLabels
                  (phaseOfGapBlock anchorBlock ::
                    rest.map phaseOfGapBlock) =
                SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                  (anchorBlock :: rest) := by
            simpa only [List.map_cons] using
              phaseLabels_map_phaseOfGapBlock (anchorBlock :: rest)
          apply BlockFinalDebtData.same
          simp [profileCountSweptListFrom, profileCountBlockCanonicalList,
            profileCountCanonicalListFrom, counts,
            takeWhile_map_phaseOfGapBlock,
            dropWhile_map_phaseOfGapBlock, activeShape',
            renderSweptCore, coreShape, renderProfileCountCore,
            phaseCoreShape', activeLabels]
      | some splitData =>
          rcases splitData with ⟨before, lastBlock, suffixBlocks⟩
          have phaseCoreShape :
              splitLastDoubledPhase
                  ((anchorBlock :: rest).map phaseOfGapBlock) =
                some
                  (before.map phaseOfGapBlock,
                    phaseOfGapBlock lastBlock,
                    suffixBlocks.map phaseOfGapBlock) := by
            rw [splitLastDoubledPhase_map_phaseOfGapBlock, coreShape]
            rfl
          have phaseCoreShape' :
              splitLastDoubledPhase
                  (phaseOfGapBlock anchorBlock ::
                    rest.map phaseOfGapBlock) =
                some
                  (before.map phaseOfGapBlock,
                    phaseOfGapBlock lastBlock,
                    suffixBlocks.map phaseOfGapBlock) := by
            simpa only [List.map_cons] using phaseCoreShape
          have facts :=
            activeFinalDebtFacts formed counts rfl anchorBlock rest
              before lastBlock suffixBlocks activeShape' coreShape
          dsimp only at facts
          obtain
            ⟨sourceWitnessed, targetWitnessed, sameSupport⟩ := facts
          let simpleBlocks :=
            blocks.takeWhile
              (fun block => !(gapBlockRepeated counts block))
          let witnesses :=
            blockDebtWitnesses simpleBlocks anchorBlock before lastBlock
          let repeatedLater :=
            repeatedLaterGapMarkers counts before lastBlock
          have repeatedLaterShape :
              phaseLabels
                  (((before.map phaseOfGapBlock ++
                    [phaseOfGapBlock lastBlock]).drop 1).filter
                      (phaseRepeated counts)) =
                repeatedLater := by
            simpa [List.map_append, repeatedLater] using
              repeatedLaterPhaseLabels_eq counts before lastBlock
          have coreRendererShape :
              renderProfileCountCore counts
                  (phaseOfGapBlock anchorBlock)
                  (rest.map phaseOfGapBlock) =
                renderSweptCorePrefix anchorBlock.marker before ++
                  [lastBlock.marker, anchorBlock.marker] ++
                  repeatedLater ++
                  SemigroupBasis.CoRoots.S5_870.gapBlockMarkers
                    suffixBlocks := by
            unfold renderProfileCountCore
            dsimp only
            rw [phaseCoreShape']
            dsimp only
            rw [
              renderProfileCountCorePrefix_map_phaseOfGapBlock,
              repeatedLaterShape,
              phaseLabels_map_phaseOfGapBlock
            ]
            rfl
          refine
            BlockFinalDebtData.active witnesses
              (SemigroupBasis.CoRoots.S5_870.gapBlockMarkers suffixBlocks)
              anchorBlock.marker before lastBlock repeatedLater
              ?_ ?_ ?_ ?_ ?_
          · simp [profileCountSweptListFrom, counts,
              activeShape', renderSweptCore, coreShape,
              witnesses, simpleBlocks, blockDebtWitnesses,
              List.append_assoc]
          · simp [profileCountBlockCanonicalList,
              profileCountCanonicalListFrom, counts,
              takeWhile_map_phaseOfGapBlock,
              dropWhile_map_phaseOfGapBlock, activeShape',
              coreRendererShape, witnesses, simpleBlocks,
              blockDebtWitnesses, repeatedLater, List.append_assoc]
          · simpa [witnesses, simpleBlocks, blockDebtWitnesses] using
              sourceWitnessed
          · simpa [witnesses, simpleBlocks, blockDebtWitnesses,
              repeatedLater] using targetWitnessed
          · simpa [repeatedLater] using sameSupport

/-! ## Gap parser and phase scanner agreement -/

private theorem scanPhases_append
    (phases : List Phase) :
    ∀ left right : List Nat,
      scanPhases phases (left ++ right) =
        scanPhases (scanPhases phases left) right
  | [], right => rfl
  | letter :: rest, right => by
      simpa [scanPhases] using
        scanPhases_append (phaseStep phases letter) rest right

private theorem markLastDoubled_append_singleton
    (earlierPhases : List Phase) (phase : Phase) :
    markLastDoubled (earlierPhases ++ [phase]) =
      earlierPhases ++ [⟨phase.label, true⟩] := by
  induction earlierPhases with
  | nil =>
      simp [markLastDoubled]
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp [markLastDoubled]
      | cons next rest =>
          change
            head :: markLastDoubled (next :: (rest ++ [phase])) =
              head :: next ::
                (rest ++ [⟨phase.label, true⟩])
          exact congrArg (List.cons head) induction

private theorem scanPhases_oldAfterDoubled
    (earlierPhases : List Phase) (marker : Nat) :
    ∀ gap : List Nat,
      (∀ letter, letter ∈ gap →
        letter ∈ marker :: phaseLabels earlierPhases) →
      scanPhases (earlierPhases ++ [⟨marker, true⟩]) gap =
        earlierPhases ++ [⟨marker, true⟩]
  | [], _ => rfl
  | letter :: rest, known => by
      have letterOld :
          letter ∈
            phaseLabels (earlierPhases ++ [⟨marker, true⟩]) := by
        simpa [phaseLabels, or_comm] using
          known letter (by simp)
      have restKnown :
          ∀ tested, tested ∈ rest →
            tested ∈ marker :: phaseLabels earlierPhases := by
        intro tested member
        exact known tested (List.Mem.tail letter member)
      have step :
          phaseStep (earlierPhases ++ [⟨marker, true⟩]) letter =
            earlierPhases ++ [⟨marker, true⟩] := by
        simp [phaseStep, letterOld,
          markLastDoubled_append_singleton]
      rw [scanPhases, step]
      exact scanPhases_oldAfterDoubled
        earlierPhases marker rest restKnown

private theorem scanPhases_knownGap
    (earlierPhases : List Phase) (marker : Nat) :
    ∀ gap : List Nat,
      (∀ letter, letter ∈ gap →
        letter ∈ marker :: phaseLabels earlierPhases) →
      scanPhases (earlierPhases ++ [⟨marker, false⟩]) gap =
        earlierPhases ++
          [⟨marker, decide (gap ≠ [])⟩]
  | [], _ => by
      simp [scanPhases]
  | letter :: rest, known => by
      have letterOld :
          letter ∈
            phaseLabels (earlierPhases ++ [⟨marker, false⟩]) := by
        simpa [phaseLabels, or_comm] using
          known letter (by simp)
      have restKnown :
          ∀ tested, tested ∈ rest →
            tested ∈ marker :: phaseLabels earlierPhases := by
        intro tested member
        exact known tested (List.Mem.tail letter member)
      have step :
          phaseStep (earlierPhases ++ [⟨marker, false⟩]) letter =
            earlierPhases ++ [⟨marker, true⟩] := by
        simp [phaseStep, letterOld,
          markLastDoubled_append_singleton]
      rw [scanPhases, step]
      simpa using
        scanPhases_oldAfterDoubled
          earlierPhases marker rest restKnown

private theorem scanPhases_renderGapBlocks
    {seen : List Nat} {phases : List Phase}
    {blocks : List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock}
    (formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed seen blocks)
    (prefixLabels :
      phaseLabels phases = seen.reverse) :
    scanPhases phases (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks) =
      phases ++ blocks.map phaseOfGapBlock := by
  induction formed generalizing phases with
  | nil seen =>
      simp [SemigroupBasis.CoRoots.S5_870.renderGapBlocks, scanPhases]
  | cons seen block rest markerFresh
      secondsSeen tail induction =>
      have markerFreshPhases :
          block.marker ∉ phaseLabels phases := by
        rw [prefixLabels]
        intro member
        apply markerFresh
        simpa using member
      have markerStep :
          phaseStep phases block.marker =
            phases ++ [⟨block.marker, false⟩] := by
        simp [phaseStep, markerFreshPhases]
      have secondsKnown :
          ∀ letter, letter ∈ block.seconds →
            letter ∈ block.marker :: phaseLabels phases := by
        intro letter member
        have old := secondsSeen letter member
        simpa [prefixLabels] using old
      have scannedGap :=
        scanPhases_knownGap phases block.marker
          block.seconds secondsKnown
      have nextLabels :
          phaseLabels
              (phases ++ [phaseOfGapBlock block]) =
            (block.marker :: seen).reverse := by
        simpa [phaseLabels, phaseOfGapBlock] using
          congrArg
            (fun labels => labels ++ [block.marker])
            prefixLabels
      have scannedRest :=
        induction
          (phases := phases ++ [phaseOfGapBlock block])
          nextLabels
      have scannedRest' :
          scanPhases
              (phases ++
                [⟨block.marker,
                  decide (block.seconds ≠ [])⟩])
              (SemigroupBasis.CoRoots.S5_870.renderGapBlocks rest) =
            phases ++
              [⟨block.marker,
                decide (block.seconds ≠ [])⟩] ++
              rest.map phaseOfGapBlock := by
        simpa only [phaseOfGapBlock] using scannedRest
      rw [SemigroupBasis.CoRoots.S5_870.renderGapBlocks, scanPhases,
        markerStep, scanPhases_append, scannedGap,
        scannedRest']
      by_cases secondsEmpty : block.seconds = []
      · simp [List.append_assoc, phaseOfGapBlock, secondsEmpty]
      · simp [List.append_assoc, phaseOfGapBlock, secondsEmpty]

private theorem scanPhases_nil_eq_phaseProfileList :
    ∀ letters : List Nat,
      scanPhases [] letters = phaseProfileList letters
  | [] => rfl
  | head :: tail => by
      simp [scanPhases, phaseStep, phaseLabels,
        phaseProfileList]

/-! ## Strictly isolated residuals -/

/-- Pure parser/scanner compatibility.  This has no semigroup reasoning:
the executable gap decomposition and the `S5_831` phase scanner assign the
same labels and doubled bits. -/
def PhaseGapProfileAgreement : Prop :=
  ∀ letters : List Nat,
    phaseProfileList letters =
      (SemigroupBasis.CoRoots.S5_870.gapBlocksList letters).map phaseOfGapBlock

/-- The executable gap parser agrees with the completed phase scanner. -/
theorem phaseGapProfileAgreement :
    PhaseGapProfileAgreement := by
  intro letters
  let blocks := SemigroupBasis.CoRoots.S5_870.gapBlocksList letters
  have formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks := by
    simpa [blocks] using SemigroupBasis.CoRoots.S5_870.gapBlocksList_wellFormed letters
  have rendered :
      SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks = letters := by
    simpa [blocks] using SemigroupBasis.CoRoots.S5_870.render_gapBlocksList letters
  have scanned :=
    scanPhases_renderGapBlocks
      (seen := [])
      (phases := [])
      (blocks := blocks)
      formed
      (by simp [phaseLabels])
  rw [rendered,
    scanPhases_nil_eq_phaseProfileList letters] at scanned
  simpa [blocks] using scanned

/-- Structural Lee--Zhang sweep on an already parsed, well-formed block
decomposition.

The only nontrivial derivational step is
`hullListDerivesMoveSeenGapToDebt`; `GapBlocksWellFormed.secondsSeen`
supplies its old-letter hypothesis.  The target deliberately retains the
entire unpermuted, uncontracted debt. -/
def BlockGapRedistribution : Prop :=
  ∀ {blocks : List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock},
    SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks →
    blocks ≠ [] →
      HullListDerives
        (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)
        (profileCountSweptListFrom blocks
          (cappedCountProfile (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)))

/-- Normalize only the final witnessed debt of an already swept block word.

Both renderers now retain the anchor in their final debts, so this stage is
one application of `hullListDerivesOfSameSupportAfterWitnesses`.  It contains
no phase-block redistribution or exceptional terminal contraction. -/
def BlockFinalDebtNormalization : Prop :=
  ∀ {blocks : List SemigroupBasis.CoRoots.S5_870.FirstOccurrenceGapBlock},
    SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks →
    blocks ≠ [] →
      HullListDerives
        (profileCountSweptListFrom blocks
          (cappedCountProfile (SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks)))
        (profileCountBlockCanonicalList blocks)

/-- Final debt normalization is now one witnessed same-support normalization.
The extra anchor retained by both renderers removes the exceptional terminal
contraction branch. -/
theorem blockFinalDebtNormalization :
    BlockFinalDebtNormalization := by
  intro blocks formed nonempty
  have data := blockFinalDebtData formed nonempty
  cases data with
  | same shape =>
      rw [shape]
      exact
        SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis :=
            SemigroupBasis.Order6Subdirect.Hull21_1_S5_831_S3_8.publishedBasis)
          _
  | active witnesses suffix anchor before lastBlock repeatedLater
      sourceShape targetShape sourceWitnessed targetWitnessed sameSupport =>
      rw [sourceShape, targetShape]
      exact
        hullListDerivesOfSameSupportAfterWitnesses
          witnesses suffix
          (anchor ::
            (SemigroupBasis.CoRoots.S5_870.gapBlockSeconds
                before.reverse ++
              lastBlock.seconds))
          (anchor :: repeatedLater)
          sourceWitnessed targetWitnessed sameSupport

/-- The original one-word canonicalization consumer. -/
def ProfileCountCanonicalization : Prop :=
  ∀ {letters : List Nat},
    letters ≠ [] →
      HullListDerives letters
        (profileCountCanonicalList letters)

/-- The two isolated derivational block obligations imply the one-word sweep.

`render_gapBlocksList` and `gapBlocksList_wellFormed` discharge all parser
side conditions, while `phaseGapProfileAgreement` identifies the target
renderer.  No one-factor normalizer is used. -/
theorem profileCountCanonicalization_of_block_sweeps
    (redistribute : BlockGapRedistribution)
    (normalizeDebt : BlockFinalDebtNormalization) :
    ProfileCountCanonicalization := by
  intro letters lettersNonempty
  let blocks := SemigroupBasis.CoRoots.S5_870.gapBlocksList letters
  have rendered :
      SemigroupBasis.CoRoots.S5_870.renderGapBlocks blocks = letters := by
    simpa [blocks] using SemigroupBasis.CoRoots.S5_870.render_gapBlocksList letters
  have blocksNonempty : blocks ≠ [] := by
    intro blocksEmpty
    apply lettersNonempty
    rw [← rendered, blocksEmpty]
    rfl
  have formed :
      SemigroupBasis.CoRoots.S5_870.GapBlocksWellFormed [] blocks := by
    simpa [blocks] using SemigroupBasis.CoRoots.S5_870.gapBlocksList_wellFormed letters
  have swept := redistribute formed blocksNonempty
  have debtNormal := normalizeDebt formed blocksNonempty
  rw [rendered] at swept debtNormal
  have blockNormal := swept.trans debtNormal
  unfold profileCountCanonicalList
  rw [phaseGapProfileAgreement letters]
  simpa [blocks, profileCountBlockCanonicalList, rendered] using blockNormal

/-- The one-word sweep closes the exact public residual from the joint
completeness module. -/
theorem profileCountNormalization_of_canonicalization
    (canonicalize : ProfileCountCanonicalization) :
    SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.ProfileCountNormalization := by
  intro left right leftNonempty rightNonempty profile counts
  have leftNormal := canonicalize leftNonempty
  have rightNormal := canonicalize rightNonempty
  have canonicalEqual :=
    profileCountCanonicalList_eq profile counts
  have rightBack :
      HullListDerives
        (profileCountCanonicalList left) right := by
    rw [canonicalEqual]
    exact rightNormal.symm
  exact leftNormal.trans rightBack

/-- Direct dependency path from the two remaining block sweeps to the public
joint residual.  Product and intersection endpoints remain deliberately
unpublished until these premises are discharged. -/
theorem profileCountNormalization_of_block_sweeps
    (redistribute : BlockGapRedistribution)
    (normalizeDebt : BlockFinalDebtNormalization) :
    SemigroupBasis.CoRoots.Order6Hull21_1JointCompleteness.ProfileCountNormalization :=
  profileCountNormalization_of_canonicalization
    (profileCountCanonicalization_of_block_sweeps
      redistribute normalizeDebt)

end Order6Hull21_1ProfileCountNormalization
end CoRoots
end SemigroupBasis

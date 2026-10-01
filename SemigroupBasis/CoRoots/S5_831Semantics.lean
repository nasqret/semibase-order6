import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.CoRoots.S5_831Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_831

open SemigroupBasis
open SemigroupBasis.Examples

theorem leftRegularBandThree_models_basis :
    Models leftRegularBandThree.semigroup basis :=
  models_of_finite_checks leftRegularBandThree (by decide)

/-- The exact zero-based embedding requested by the structural certificate:
`0 -> 0`, `1 -> 3`, `2 -> 2`. -/
def firstOccurrenceEmbedding :
    Embedding leftRegularBandThree.semigroup
      Generated.Catalogue.S5_831.table.semigroup where
  toFun := fun value =>
    if value = (0 : Fin 3) then (0 : Fin 5)
    else if value = (1 : Fin 3) then (3 : Fin 5)
    else (2 : Fin 5)
  map_mul := by
    intro left right
    exact by decide +revert
  injective := by
    intro left right equal
    exact by decide +revert

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_831.table.semigroup basis :=
  models_of_finite_checks
    Generated.Catalogue.S5_831.table (by decide)

/-- The requested one-based separator states
`P=4,T=2,D=1,F=5,S=3`, represented here zero-based as
`P=3,T=1,D=0,F=4,S=2`. The products are
`PP=P`, `PT=T`, `TT=D`, `TP=D`, `TF=S`, and `D/F/S` are left zeros. -/
theorem semanticStateProducts :
    Generated.Catalogue.S5_831.mul 3 3 = 3 ∧
      Generated.Catalogue.S5_831.mul 3 1 = 1 ∧
      Generated.Catalogue.S5_831.mul 1 1 = 0 ∧
      Generated.Catalogue.S5_831.mul 1 3 = 0 ∧
      Generated.Catalogue.S5_831.mul 1 4 = 2 ∧
      (∀ value : Fin 5,
        Generated.Catalogue.S5_831.mul 0 value = 0) ∧
      (∀ value : Fin 5,
        Generated.Catalogue.S5_831.mul 4 value = 4) ∧
      (∀ value : Fin 5,
        Generated.Catalogue.S5_831.mul 2 value = 2) := by
  decide

/-- The scanner labels are exactly the sequence of first occurrences. The
proof uses normalization plus the left-regular-band semantic separator. -/
theorem phaseLabels_phaseProfile_eq_firstOccurrenceSequence
    (word : Word Nat) :
    phaseLabels (phaseProfile word) =
      firstOccurrenceSequence word.toList := by
  let identity : Identity Nat :=
    ⟨word, canonicalWord word⟩
  have valid :
      identity.SatisfiedBy leftRegularBandThree.semigroup := by
    intro valuation
    exact (derivesCanonical word).sound
      leftRegularBandThree_models_basis valuation
  have order :=
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity valid
  have canonicalOrder :
      firstOccurrenceSequence
          (renderPhases (phaseProfile word)) =
        phaseLabels (phaseProfile word) :=
    firstOccurrenceSequence_renderPhases
      (phaseLabels_phaseProfile_nodup word)
  change
    firstOccurrenceSequence word.toList =
      firstOccurrenceSequence (canonicalWord word).toList at order
  rw [toList_canonicalWord] at order
  exact (order.trans canonicalOrder).symm

theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_831.table.semigroup) :
    firstOccurrenceSequence identity.lhs.toList =
      firstOccurrenceSequence identity.rhs.toList := by
  exact
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity
      (firstOccurrenceEmbedding.pullback_identity identity valid)

private theorem eval_phaseWord_pass
    (valuation : Nat → Fin 5) (phase : Phase)
    (pass : valuation phase.label = 3) :
    Generated.Catalogue.S5_831.table.semigroup.eval
        valuation (phaseWord phase) = (3 : Fin 5) := by
  rcases phase with ⟨label, doubled⟩
  cases doubled <;>
    simp [phaseWord, pass, Semigroup.eval,
      Generated.Catalogue.S5_831.table,
      Generated.Catalogue.S5_831.mul,
      FiniteTable.semigroup]

private theorem eval_phaseWord_transient
    (valuation : Nat → Fin 5) (phase : Phase)
    (transient : valuation phase.label = 1) :
    Generated.Catalogue.S5_831.table.semigroup.eval
        valuation (phaseWord phase) =
      if phase.doubled then (0 : Fin 5) else (1 : Fin 5) := by
  rcases phase with ⟨label, doubled⟩
  cases doubled <;>
    simp [phaseWord, transient, Semigroup.eval,
      Generated.Catalogue.S5_831.table,
      Generated.Catalogue.S5_831.mul,
      FiniteTable.semigroup]

private theorem eval_phaseWord_fresh
    (valuation : Nat → Fin 5) (phase : Phase)
    (fresh : valuation phase.label = 4) :
    Generated.Catalogue.S5_831.table.semigroup.eval
        valuation (phaseWord phase) = (4 : Fin 5) := by
  rcases phase with ⟨label, doubled⟩
  cases doubled <;>
    simp [phaseWord, fresh, Semigroup.eval,
      Generated.Catalogue.S5_831.table,
      Generated.Catalogue.S5_831.mul,
      FiniteTable.semigroup]

private theorem eval_profileWord_fresh
    (valuation : Nat → Fin 5) :
    ∀ (phase : Phase) (rest : List Phase),
      valuation phase.label = 4 →
      (∀ next, next ∈ rest → valuation next.label = 4) →
      Generated.Catalogue.S5_831.table.semigroup.eval
          valuation (profileWord phase rest) = (4 : Fin 5)
  | phase, [], phaseFresh, _ =>
      eval_phaseWord_fresh valuation phase phaseFresh
  | phase, next :: tail, phaseFresh, restFresh => by
      rw [profileWord, Semigroup.eval_append,
        eval_phaseWord_fresh valuation phase phaseFresh,
        eval_profileWord_fresh valuation next tail
          (restFresh next (List.Mem.head tail))
          (fun later member =>
            restFresh later (List.Mem.tail next member))]
      rfl

private def occupancyValue
    (doubled : Bool) (tail : List Phase) : Fin 5 :=
  if doubled then
    0
  else if tail = [] then
    1
  else
    2

private theorem eval_profileWord_selected
    (valuation : Nat → Fin 5) (current : Phase)
    (tail : List Phase)
    (currentTransient : valuation current.label = 1)
    (tailFresh :
      ∀ phase, phase ∈ tail → valuation phase.label = 4) :
    Generated.Catalogue.S5_831.table.semigroup.eval
        valuation (profileWord current tail) =
      occupancyValue current.doubled tail := by
  cases tail with
  | nil =>
      simpa [occupancyValue] using
        eval_phaseWord_transient
          valuation current currentTransient
  | cons next rest =>
      rw [profileWord, Semigroup.eval_append,
        eval_phaseWord_transient
          valuation current currentTransient,
        eval_profileWord_fresh valuation next rest
          (tailFresh next (List.Mem.head rest))
          (fun later member =>
            tailFresh later (List.Mem.tail next member))]
      cases current.doubled <;>
        simp [occupancyValue,
          Generated.Catalogue.S5_831.table,
          Generated.Catalogue.S5_831.mul,
          FiniteTable.semigroup]

private def prefixedProfileWord
    (prior : List Phase) (current : Phase)
    (tail : List Phase) : Word Nat :=
  match prior with
  | [] => profileWord current tail
  | phase :: rest =>
      profileWord phase (rest ++ current :: tail)

private theorem prefixedProfileWord_cons
    (phase : Phase) (prior : List Phase)
    (current : Phase) (tail : List Phase) :
    prefixedProfileWord (phase :: prior) current tail =
      phaseWord phase ++
        prefixedProfileWord prior current tail := by
  cases prior <;> rfl

private theorem eval_prefixedProfileWord
    (valuation : Nat → Fin 5) :
    ∀ (prior : List Phase) (current : Phase)
        (tail : List Phase),
      (∀ phase, phase ∈ prior →
        valuation phase.label = 3) →
      valuation current.label = 1 →
      (∀ phase, phase ∈ tail →
        valuation phase.label = 4) →
      Generated.Catalogue.S5_831.table.semigroup.eval
          valuation
          (prefixedProfileWord prior current tail) =
        occupancyValue current.doubled tail
  | [], current, tail, _, currentTransient, tailFresh =>
      eval_profileWord_selected
        valuation current tail currentTransient tailFresh
  | phase :: prior, current, tail,
      prefixPass, currentTransient, tailFresh => by
      rw [prefixedProfileWord_cons,
        Semigroup.eval_append,
        eval_phaseWord_pass valuation phase
          (prefixPass phase (List.Mem.head prior)),
        eval_prefixedProfileWord valuation prior current tail
          (fun earlier member =>
            prefixPass earlier (List.Mem.tail phase member))
          currentTransient tailFresh]
      cases current.doubled <;>
        by_cases empty : tail = [] <;>
          simp [occupancyValue, empty,
            Generated.Catalogue.S5_831.table,
            Generated.Catalogue.S5_831.mul,
            FiniteTable.semigroup]

private theorem profileWordOr_eq_prefixed
    (fallback : Nat) (prior : List Phase)
    (current : Phase) (tail : List Phase) :
    profileWordOr fallback
        (prior ++ current :: tail) =
      prefixedProfileWord prior current tail := by
  cases prior <;> rfl

private theorem eval_profileWordOr_separator
    (fallback : Nat) (valuation : Nat → Fin 5)
    (prior : List Phase) (current : Phase)
    (tail : List Phase)
    (prefixPass :
      ∀ phase, phase ∈ prior →
        valuation phase.label = 3)
    (currentTransient : valuation current.label = 1)
    (tailFresh :
      ∀ phase, phase ∈ tail →
        valuation phase.label = 4) :
    Generated.Catalogue.S5_831.table.semigroup.eval valuation
        (profileWordOr fallback
          (prior ++ current :: tail)) =
      occupancyValue current.doubled tail := by
  rw [profileWordOr_eq_prefixed]
  exact eval_prefixedProfileWord valuation prior current tail
    prefixPass currentTransient tailFresh

private def phaseSeparator
    (prior : List Phase) (current : Nat) :
    Nat → Fin 5 :=
  fun letter =>
    if letter = current then
      1
    else if letter ∈ phaseLabels prior then
      3
    else
      4

private theorem not_mem_parts_of_nodup_split
    {letters before after : List Nat} {letter : Nat}
    (nodup : letters.Nodup)
    (split : letters = before ++ letter :: after) :
    letter ∉ before ∧ letter ∉ after := by
  have splitNodup :
      (before ++ letter :: after).Nodup := by
    rw [← split]
    exact nodup
  have appendData := List.nodup_append.mp splitNodup
  constructor
  · intro member
    exact appendData.2.2
      letter member letter (by simp) rfl
  · exact (List.nodup_cons.mp appendData.2.1).1

private theorem phaseLabel_mem
    {phase : Phase} {phases : List Phase}
    (member : phase ∈ phases) :
    phase.label ∈ phaseLabels phases :=
  List.mem_map.mpr ⟨phase, member, rfl⟩

private theorem tail_nil_iff_of_labels_eq
    {left right : List Phase}
    (equal : phaseLabels left = phaseLabels right) :
    left = [] ↔ right = [] := by
  constructor
  · intro leftNil
    subst left
    cases right with
    | nil => rfl
    | cons phase rest =>
        simp [phaseLabels] at equal
  · intro rightNil
    subst right
    cases left with
    | nil => rfl
    | cons phase rest =>
        simp [phaseLabels] at equal

private theorem doubled_eq_of_occupancyValue_eq
    {leftTail rightTail : List Phase}
    (sameEmpty : leftTail = [] ↔ rightTail = [])
    {leftBit rightBit : Bool}
    (equal :
      occupancyValue leftBit leftTail =
        occupancyValue rightBit rightTail) :
    leftBit = rightBit := by
  by_cases leftEmpty : leftTail = []
  · have rightEmpty := sameEmpty.mp leftEmpty
    subst leftTail
    subst rightTail
    cases leftBit <;> cases rightBit <;>
      simp [occupancyValue] at equal ⊢
  · have rightNonempty : rightTail ≠ [] := by
      intro rightEmpty
      exact leftEmpty (sameEmpty.mpr rightEmpty)
    cases leftBit <;> cases rightBit <;>
      simp [occupancyValue, leftEmpty, rightNonempty] at equal ⊢

private theorem phaseProfiles_eq_aux
    (leftFallback rightFallback : Nat) :
    ∀ (prior left right : List Phase),
      phaseLabels left = phaseLabels right →
      (phaseLabels (prior ++ left)).Nodup →
      (phaseLabels (prior ++ right)).Nodup →
      (∀ valuation : Nat → Fin 5,
        Generated.Catalogue.S5_831.table.semigroup.eval valuation
            (profileWordOr leftFallback (prior ++ left)) =
          Generated.Catalogue.S5_831.table.semigroup.eval valuation
            (profileWordOr rightFallback (prior ++ right))) →
      left = right
  | prior, [], right, labelsEqual, _, _, _ => by
      cases right with
      | nil =>
          rfl
      | cons phase rest =>
          simp [phaseLabels] at labelsEqual
  | prior, leftPhase :: leftTail, right,
      labelsEqual, leftNodup, rightNodup, evalEqual => by
      cases right with
      | nil =>
          simp [phaseLabels] at labelsEqual
      | cons rightPhase rightTail =>
          rcases leftPhase with ⟨label, leftBit⟩
          rcases rightPhase with ⟨rightLabel, rightBit⟩
          change
            label :: phaseLabels leftTail =
              rightLabel :: phaseLabels rightTail at labelsEqual
          have labelEqual : label = rightLabel :=
            (List.cons.inj labelsEqual).1
          have tailLabelsEqual :
              phaseLabels leftTail =
                phaseLabels rightTail :=
            (List.cons.inj labelsEqual).2
          subst rightLabel
          have leftSplit :
              phaseLabels
                  (prior ++
                    (⟨label, leftBit⟩ : Phase) :: leftTail) =
                phaseLabels prior ++
                  label :: phaseLabels leftTail := by
            simp [phaseLabels]
          have rightSplit :
              phaseLabels
                  (prior ++
                    (⟨label, rightBit⟩ : Phase) :: rightTail) =
                phaseLabels prior ++
                  label :: phaseLabels rightTail := by
            simp [phaseLabels]
          have leftParts :=
            not_mem_parts_of_nodup_split leftNodup leftSplit
          have rightParts :=
            not_mem_parts_of_nodup_split rightNodup rightSplit
          have leftSplitNodup :
              (phaseLabels prior ++
                label :: phaseLabels leftTail).Nodup := by
            rw [← leftSplit]
            exact leftNodup
          have rightSplitNodup :
              (phaseLabels prior ++
                label :: phaseLabels rightTail).Nodup := by
            rw [← rightSplit]
            exact rightNodup
          have leftAppend :=
            List.nodup_append.mp leftSplitNodup
          have rightAppend :=
            List.nodup_append.mp rightSplitNodup
          let valuation :=
            phaseSeparator prior label
          have prefixPass :
              ∀ phase, phase ∈ prior →
                valuation phase.label = 3 := by
            intro phase member
            have labelMember :=
              phaseLabel_mem member
            have different : phase.label ≠ label := by
              intro equal
              apply leftParts.1
              simpa [equal] using labelMember
            simp [valuation, phaseSeparator,
              different, labelMember]
          have currentTransient :
              valuation label = 1 := by
            simp [valuation, phaseSeparator]
          have leftTailFresh :
              ∀ phase, phase ∈ leftTail →
                valuation phase.label = 4 := by
            intro phase member
            have labelMember :=
              phaseLabel_mem member
            have different : phase.label ≠ label := by
              intro equal
              apply leftParts.2
              simpa [equal] using labelMember
            have absentPrefix :
                phase.label ∉ phaseLabels prior := by
              intro prefixMember
              exact leftAppend.2.2
                phase.label prefixMember
                phase.label (by simp [labelMember]) rfl
            simp [valuation, phaseSeparator,
              different, absentPrefix]
          have rightTailFresh :
              ∀ phase, phase ∈ rightTail →
                valuation phase.label = 4 := by
            intro phase member
            have labelMember :=
              phaseLabel_mem member
            have different : phase.label ≠ label := by
              intro equal
              apply rightParts.2
              simpa [equal] using labelMember
            have absentPrefix :
                phase.label ∉ phaseLabels prior := by
              intro prefixMember
              exact rightAppend.2.2
                phase.label prefixMember
                phase.label (by simp [labelMember]) rfl
            simp [valuation, phaseSeparator,
              different, absentPrefix]
          have evaluated := evalEqual valuation
          rw [eval_profileWordOr_separator
                leftFallback valuation prior
                ⟨label, leftBit⟩ leftTail
                prefixPass currentTransient leftTailFresh,
              eval_profileWordOr_separator
                rightFallback valuation prior
                ⟨label, rightBit⟩ rightTail
                prefixPass currentTransient rightTailFresh] at evaluated
          have bitEqual : leftBit = rightBit :=
            doubled_eq_of_occupancyValue_eq
              (tail_nil_iff_of_labels_eq tailLabelsEqual)
              evaluated
          subst rightBit
          have tailsEqual :=
            phaseProfiles_eq_aux leftFallback rightFallback
              (prior ++ [⟨label, leftBit⟩])
              leftTail rightTail
              tailLabelsEqual
              (by
                simpa [List.append_assoc] using leftNodup)
              (by
                simpa [List.append_assoc] using rightNodup)
              (fun nextValuation => by
                simpa [List.append_assoc] using
                  evalEqual nextValuation)
          rw [tailsEqual]
termination_by
  _ left _ => left.length

/-- Every identity valid in `S5_831` preserves the complete first-occurrence
phase occupancy profile. -/
theorem valid_samePhaseOccupancySignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_831.table.semigroup) :
    SamePhaseOccupancySignature identity.lhs identity.rhs := by
  change phaseProfile identity.lhs = phaseProfile identity.rhs
  have firstOccurrences :=
    valid_firstOccurrenceSequence_eq identity valid
  have labelsEqual :
      phaseLabels (phaseProfile identity.lhs) =
        phaseLabels (phaseProfile identity.rhs) := by
    exact
      (phaseLabels_phaseProfile_eq_firstOccurrenceSequence
          identity.lhs).trans <|
        firstOccurrences.trans <|
          (phaseLabels_phaseProfile_eq_firstOccurrenceSequence
            identity.rhs).symm
  have canonicalEvalEqual :
      ∀ valuation : Nat → Fin 5,
        Generated.Catalogue.S5_831.table.semigroup.eval valuation
            (canonicalWord identity.lhs) =
          Generated.Catalogue.S5_831.table.semigroup.eval valuation
            (canonicalWord identity.rhs) := by
    intro valuation
    have leftSound :=
      (derivesCanonical identity.lhs).sound models valuation
    have rightSound :=
      (derivesCanonical identity.rhs).sound models valuation
    exact leftSound.symm.trans <|
      (valid valuation).trans rightSound
  apply phaseProfiles_eq_aux
      identity.lhs.head identity.rhs.head
      [] (phaseProfile identity.lhs)
      (phaseProfile identity.rhs)
  · exact labelsEqual
  · simpa using phaseLabels_phaseProfile_nodup identity.lhs
  · simpa using phaseLabels_phaseProfile_nodup identity.rhs
  · intro valuation
    simpa [canonicalWord] using canonicalEvalEqual valuation

end SemigroupBasis.CoRoots.S5_831

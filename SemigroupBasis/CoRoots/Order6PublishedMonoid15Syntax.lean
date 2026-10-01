import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_870Invariant
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid15

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

/-! ## Proposition 15.1, with every starred deletion expanded -/

def xhytxy : Word Nat := w 0 [1, 2, 3, 0, 2]
def xhytyx : Word Nat := w 0 [1, 2, 3, 2, 0]
def xhyxy : Word Nat := w 0 [1, 2, 0, 2]
def xhyyx : Word Nat := w 0 [1, 2, 2, 0]
def xx : Word Nat := w 0 [0]
def xxx : Word Nat := w 0 [0, 0]
def xxyy : Word Nat := w 0 [0, 2, 2]
def xxyyx : Word Nat := w 0 [0, 2, 2, 0]
def xytxy : Word Nat := w 0 [2, 3, 0, 2]
def xytyx : Word Nat := w 0 [2, 3, 2, 0]
def xyx : Word Nat := w 0 [2, 0]
def xyxx : Word Nat := w 0 [2, 0, 0]
def xyxy : Word Nat := w 0 [2, 0, 2]
def xyyx : Word Nat := w 0 [2, 2, 0]

def sortGeneralLaw : Identity Nat := ⟨xhytxy, xhytyx⟩
def sortFinalGapEmptyLaw : Identity Nat := ⟨xhyxy, xhyyx⟩
def powerLaw : Identity Nat := ⟨xx, xxx⟩
def squareReturnLaw : Identity Nat := ⟨xxyy, xxyyx⟩
def sortInitialGapEmptyLaw : Identity Nat := ⟨xytxy, xytyx⟩
def finalGapCapLaw : Identity Nat := ⟨xyx, xyxx⟩
def sortBothEmptyLaw : Identity Nat := ⟨xyxy, xyyx⟩

/-- The direct seven-law Lee--Li Proposition 15.1 basis, in source-contract
order after expanding the starred deletions. -/
def basis : List (Identity Nat) :=
  [sortGeneralLaw, sortFinalGapEmptyLaw, powerLaw, squareReturnLaw,
    sortInitialGapEmptyLaw, finalGapCapLaw, sortBothEmptyLaw]

/-- Route-facing opposite orientation. -/
def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def finiteBasis : List (Identity (Fin 4)) :=
  basis.map fun identity => identity.map toFinFour

private theorem basis_roundTrip_checked :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

private theorem basis_roundTrip
    (identity : Identity Nat) (member : identity ∈ basis) :
    (identity.map toFinFour).map Fin.val = identity := by
  exact of_decide_eq_true <|
    (List.all_eq_true.mp basis_roundTrip_checked) identity member

/-- Finite checking of the four displayed variables proves soundness of the
literal seven-law system for an exact finite table. -/
theorem models_of_finite_checks
    (candidate : FiniteTable)
    (checked : finiteBasis.all candidate.checkIdentity = true) :
    Models candidate.semigroup basis := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ finiteBasis :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  rw [basis_roundTrip identity member] at finiteValid
  exact finiteValid

/-! ## Primitive word derivations -/

private def instantiateFourWords
    (u h v t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => h
  | 2 => v
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

private theorem basisSortGeneral :
    Derives basis xhytxy xhytyx :=
  Derives.fromBasis (e := sortGeneralLaw) (by simp [basis])

private theorem basisSortFinalGapEmpty :
    Derives basis xhyxy xhyyx :=
  Derives.fromBasis (e := sortFinalGapEmptyLaw) (by simp [basis])

private theorem basisPower :
    Derives basis xx xxx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisSquareReturn :
    Derives basis xxyy xxyyx :=
  Derives.fromBasis (e := squareReturnLaw) (by simp [basis])

private theorem basisSortInitialGapEmpty :
    Derives basis xytxy xytyx :=
  Derives.fromBasis (e := sortInitialGapEmptyLaw) (by simp [basis])

private theorem basisFinalGapCap :
    Derives basis xyx xyxx :=
  Derives.fromBasis (e := finalGapCapLaw) (by simp [basis])

private theorem basisSortBothEmpty :
    Derives basis xyxy xyyx :=
  Derives.fromBasis (e := sortBothEmptyLaw) (by simp [basis])

theorem derivesSortGeneral (u h v t : Word Nat) :
    Derives basis (((((u ++ h) ++ v) ++ t) ++ u) ++ v)
      (((((u ++ h) ++ v) ++ t) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSortGeneral (instantiateFourWords u h v t)
  simpa [xhytxy, xhytyx, w, instantiateFourWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesSortFinalGapEmpty (u h v : Word Nat) :
    Derives basis ((((u ++ h) ++ v) ++ u) ++ v)
      ((((u ++ h) ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSortFinalGapEmpty
      (instantiateFourWords u h v v)
  simpa [xhyxy, xhyyx, w, instantiateFourWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesPowerExpansion (u : Word Nat) :
    Derives basis (u ++ u) ((u ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateFourWords u u u u)
  simpa [xx, xxx, w, instantiateFourWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesSquareReturnExpansion (u v : Word Nat) :
    Derives basis ((u ++ u) ++ (v ++ v))
      (((u ++ u) ++ (v ++ v)) ++ u) := by
  have substituted :=
    Derives.subst basisSquareReturn (instantiateFourWords u u v v)
  simpa [xxyy, xxyyx, w, instantiateFourWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesSortInitialGapEmpty (u v t : Word Nat) :
    Derives basis ((((u ++ v) ++ t) ++ u) ++ v)
      ((((u ++ v) ++ t) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSortInitialGapEmpty
      (instantiateFourWords u u v t)
  simpa [xytxy, xytyx, w, instantiateFourWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesFinalGapExpansion (u v : Word Nat) :
    Derives basis ((u ++ v) ++ u) (((u ++ v) ++ u) ++ u) := by
  have substituted :=
    Derives.subst basisFinalGapCap (instantiateFourWords u u v v)
  simpa [xyx, xyxx, w, instantiateFourWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

theorem derivesSortBothEmpty (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have substituted :=
    Derives.subst basisSortBothEmpty (instantiateFourWords u u v v)
  simpa [xyxy, xyyx, w, instantiateFourWords, Word.bind,
    Word.singleton, Word.append, Word.append_assoc] using substituted

/-! ## Reused first-occurrence gap parser and basis-specific sorting -/

abbrev FirstOccurrenceGapBlock :=
  S5_870.FirstOccurrenceGapBlock

abbrev gapBlocksList := S5_870.gapBlocksList
abbrev renderGapBlocks := S5_870.renderGapBlocks
abbrev gapBlockMarkers := S5_870.gapBlockMarkers
abbrev gapBlockSeconds := S5_870.gapBlockSeconds
abbrev GapBlocksWellFormed := S5_870.GapBlocksWellFormed

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons := S5_107.listWordOfCons

private theorem listDerivesSortBothEmpty
    (first second : Nat) :
    ListDerives [first, second, first, second]
      [first, second, second, first] := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortBothEmpty
          (Word.singleton first) (Word.singleton second)))

private theorem listDerivesSortInitialGapEmpty
    (first second gapHead : Nat) (gapTail : List Nat) :
    ListDerives
      ([first, second] ++ (gapHead :: gapTail) ++ [first, second])
      ([first, second] ++ (gapHead :: gapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortInitialGapEmpty
          (Word.singleton first) (Word.singleton second)
          (listWordOfCons gapHead gapTail)))

private theorem listDerivesSortFinalGapEmpty
    (first gapHead second : Nat) (gapTail : List Nat) :
    ListDerives
      ([first] ++ (gapHead :: gapTail) ++ [second, first, second])
      ([first] ++ (gapHead :: gapTail) ++ [second, second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortFinalGapEmpty
          (Word.singleton first) (listWordOfCons gapHead gapTail)
          (Word.singleton second)))

private theorem listDerivesSortGeneral
    (first firstGapHead second secondGapHead : Nat)
    (firstGapTail secondGapTail : List Nat) :
    ListDerives
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [first, second])
      ([first] ++ (firstGapHead :: firstGapTail) ++ [second] ++
        (secondGapHead :: secondGapTail) ++ [second, first]) := by
  simpa [listWordOfCons, Word.singleton, Word.append,
    Word.append_assoc, List.append_assoc] using
      (S5_107.ListDerives.ofWord (basis := basis)
        (derivesSortGeneral
          (Word.singleton first) (listWordOfCons firstGapHead firstGapTail)
          (Word.singleton second)
          (listWordOfCons secondGapHead secondGapTail)))

/-- The four expanded sort laws swap adjacent displayed later occurrences. -/
theorem listDerivesSwapDisplayedSeconds
    (first second : Nat)
    (before firstGap secondGap after : List Nat) :
    ListDerives
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [first, second] ++ after)
      (before ++ [first] ++ firstGap ++ [second] ++ secondGap ++
        [second, first] ++ after) := by
  cases firstGap with
  | nil =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortBothEmpty first second)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortInitialGapEmpty
                first second secondGapHead secondGapTail)
  | cons firstGapHead firstGapTail =>
      cases secondGap with
      | nil =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortFinalGapEmpty
                first firstGapHead second firstGapTail)
      | cons secondGapHead secondGapTail =>
          simpa [List.append_assoc] using
            S5_107.ListDerives.context before after
              (listDerivesSortGeneral first firstGapHead second
                secondGapHead firstGapTail secondGapTail)

/-- Once both letters occur in the stem, their adjacent later occurrences
can be swapped without invoking either false S5 cap law. -/
theorem listDerivesSwapAfterSeen
    (stem suffix : List Nat) (left right : Nat)
    (leftSeen : left ∈ stem) (rightSeen : right ∈ stem) :
    ListDerives (stem ++ [left, right] ++ suffix)
      (stem ++ [right, left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
      List.mem_iff_append.mp leftSeen
    have rightInSplit : right ∈ leftBefore ∨ right ∈ leftAfter := by
      rw [prefixSplit] at rightSeen
      rcases List.mem_append.mp rightSeen with beforeMember | afterMember
      · exact Or.inl beforeMember
      · rcases List.mem_cons.mp afterMember with atLeft | inAfter
        · exact False.elim (equal atLeft.symm)
        · exact Or.inr inAfter
    rcases rightInSplit with rightBefore | rightAfter
    · obtain ⟨before, middle, beforeSplit⟩ :=
        List.mem_iff_append.mp rightBefore
      have displayed :=
        listDerivesSwapDisplayedSeconds
          right left before middle leftAfter suffix
      simpa [prefixSplit, beforeSplit, List.append_assoc] using
        displayed.symm
    · obtain ⟨middle, tail, afterSplit⟩ :=
        List.mem_iff_append.mp rightAfter
      simpa [prefixSplit, afterSplit, List.append_assoc] using
        listDerivesSwapDisplayedSeconds
          left right leftBefore middle tail suffix

/-- Reorder an arbitrary later block when every displayed letter has already
occurred in the fixed stem. -/
theorem listDerivesPermuteAfterSeen
    (stem suffix : List Nat) {source target : List Nat}
    (sourceSeen : ∀ letter, letter ∈ source → letter ∈ stem)
    (permutation : source.Perm target) :
    ListDerives (stem ++ source ++ suffix)
      (stem ++ target ++ suffix) := by
  induction permutation generalizing stem with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ induction =>
      have derivation := induction (stem ++ [head]) (by
        intro letter member
        exact List.mem_append.mpr <| Or.inl <|
          sourceSeen letter (List.Mem.tail head member))
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have firstSeen : first ∈ stem := sourceSeen first (by simp)
      have secondSeen : second ∈ stem := sourceSeen second (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapAfterSeen stem (rest ++ suffix)
          second first secondSeen firstSeen
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation := firstInduction stem sourceSeen
      have secondDerivation := secondInduction stem (by
        intro letter member
        exact sourceSeen letter ((firstPermutation.mem_iff).mpr member))
      exact firstDerivation.trans secondDerivation

/-! ## Post-second-occurrence marker state -/

/-- The common seven-state refinement of the J and K marker computations.
The `directTail` state decodes to one-based 1 in J and one-based 3 in K;
all other states have the same zero-based decoding in the two tables. -/
inductive PostSecondState where
  | neutral
  | selected
  | protector
  | terminator
  | directTail
  | zero
  | two
deriving DecidableEq, Repr

inductive MarkerLetter where
  | neutral
  | selected
  | protector
  | terminator
deriving DecidableEq, Repr

def markerLetter (selected protector : Nat)
    (terminator : Option Nat) (letter : Nat) : MarkerLetter :=
  if letter = selected then .selected
  else if letter = protector then .protector
  else match terminator with
    | some final => if letter = final then .terminator else .neutral
    | none => .neutral

/-- The Lee--Li marker valuation: selected, protector, optional next marker,
and all erased variables are sent to one-based 4, 2, 6, and 5. -/
def markerValuation (selected protector : Nat)
    (terminator : Option Nat) : Nat → Fin 6 :=
  fun letter =>
    match markerLetter selected protector terminator letter with
    | .neutral => 4
    | .selected => 3
    | .protector => 1
    | .terminator => 5

/-- A second target valuation used only for semantic separation. It differs
from the published marker by sending the terminator to zero-based element 2. -/
def markerValuationAlt (selected protector : Nat)
    (terminator : Option Nat) : Nat → Fin 6 :=
  fun letter =>
    match markerLetter selected protector terminator letter with
    | .neutral => 4
    | .selected => 3
    | .protector => 1
    | .terminator => 2

def PostSecondState.step : PostSecondState → MarkerLetter → PostSecondState
  | .neutral, .neutral => .neutral
  | .neutral, .selected => .selected
  | .neutral, .protector => .protector
  | .neutral, .terminator => .terminator
  | .selected, .neutral => .selected
  | .selected, .selected => .selected
  | .selected, .protector => .protector
  | .selected, .terminator => .directTail
  | .protector, .neutral => .protector
  | .protector, .selected => .zero
  | .protector, .protector => .zero
  | .protector, .terminator => .two
  | .terminator, _ => .terminator
  | .directTail, _ => .directTail
  | .zero, _ => .zero
  | .two, _ => .two

def postSecondStateList
    (letters : List Nat) (selected protector : Nat)
    (terminator : Option Nat) : PostSecondState :=
  letters.foldl
    (fun state letter =>
      state.step (markerLetter selected protector terminator letter))
    .neutral

def postSecondState
    (word : Word Nat) (selected protector : Nat)
    (terminator : Option Nat) : PostSecondState :=
  postSecondStateList word.toList selected protector terminator

def PostSecondState.decodeJ : PostSecondState → Fin 6
  | .neutral => 4
  | .selected => 3
  | .protector => 1
  | .terminator => 5
  | .directTail => 0
  | .zero => 0
  | .two => 2

def PostSecondState.decodeK : PostSecondState → Fin 6
  | .neutral => 4
  | .selected => 3
  | .protector => 1
  | .terminator => 5
  | .directTail => 2
  | .zero => 0
  | .two => 2

def PostSecondState.decodeJAlt : PostSecondState → Fin 6
  | .neutral => 4
  | .selected => 3
  | .protector => 1
  | .terminator => 2
  | .directTail => 2
  | .zero => 0
  | .two => 0

def PostSecondState.decodeKAlt : PostSecondState → Fin 6
  | .neutral => 4
  | .selected => 3
  | .protector => 1
  | .terminator => 2
  | .directTail => 2
  | .zero => 0
  | .two => 0

theorem PostSecondState.eq_of_decodeJ_pair
    {left right : PostSecondState}
    (primary : left.decodeJ = right.decodeJ)
    (alternate : left.decodeJAlt = right.decodeJAlt) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [PostSecondState.decodeJ, PostSecondState.decodeJAlt]

theorem PostSecondState.eq_of_decodeK_pair
    {left right : PostSecondState}
    (primary : left.decodeK = right.decodeK)
    (alternate : left.decodeKAlt = right.decodeKAlt) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [PostSecondState.decodeK, PostSecondState.decodeKAlt]

def postSecondProfile
    (word : Word Nat) : Nat → Nat → Option Nat → PostSecondState :=
  fun selected protector terminator =>
    postSecondState word selected protector terminator

def postSecondProfileList
    (letters : List Nat) : Nat → Nat → Option Nat → PostSecondState :=
  fun selected protector terminator =>
    postSecondStateList letters selected protector terminator

/-- The S5 gap signature together with the state that remains observable
after a selected letter's second occurrence. Unlike the old cap signature,
this profile does not discard third and later occurrences. -/
structure RefinedGapSignature where
  gap : S5_870.GapSignature
  postSecond : Nat → Nat → Option Nat → PostSecondState

def refinedGapSignature (word : Word Nat) : RefinedGapSignature where
  gap := S5_870.gapSignature word
  postSecond := postSecondProfile word

def refinedGapSignatureList (letters : List Nat) : RefinedGapSignature where
  gap := S5_870.gapSignatureList letters
  postSecond := postSecondProfileList letters

@[simp]
theorem refinedGapSignatureList_toList (word : Word Nat) :
    refinedGapSignatureList word.toList = refinedGapSignature word := rfl

theorem RefinedGapSignature.ext
    {left right : RefinedGapSignature}
    (gap : left.gap = right.gap)
    (postSecond : left.postSecond = right.postSecond) :
    left = right := by
  cases left
  cases right
  simp_all

/-! ## Soundness of the refined marker state -/

def PostSecondState.mul :
    PostSecondState → PostSecondState → PostSecondState
  | .neutral, right => right
  | .selected, .neutral => .selected
  | .selected, .selected => .selected
  | .selected, .protector => .protector
  | .selected, .terminator => .directTail
  | .selected, .directTail => .directTail
  | .selected, .zero => .zero
  | .selected, .two => .two
  | .protector, .neutral => .protector
  | .protector, .selected => .zero
  | .protector, .protector => .zero
  | .protector, .terminator => .two
  | .protector, .directTail => .zero
  | .protector, .zero => .zero
  | .protector, .two => .zero
  | .terminator, _ => .terminator
  | .directTail, _ => .directTail
  | .zero, _ => .zero
  | .two, _ => .two

def postSecondSemigroup : Semigroup PostSecondState where
  mul := PostSecondState.mul
  assoc := by
    intro left middle right
    cases left <;> cases middle <;> cases right <;> rfl

private def row7
    (c0 c1 c2 c3 c4 c5 c6 column : Fin 7) : Fin 7 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else
            if column = 5 then c5 else c6

private def postSecondFiniteMul (left right : Fin 7) : Fin 7 :=
  if left = 0 then row7 0 1 2 3 4 5 6 right else
    if left = 1 then row7 1 1 2 4 4 5 6 right else
      if left = 2 then row7 2 5 5 6 5 5 5 right else
        if left = 3 then row7 3 3 3 3 3 3 3 right else
          if left = 4 then row7 4 4 4 4 4 4 4 right else
            if left = 5 then row7 5 5 5 5 5 5 5 right else
              row7 6 6 6 6 6 6 6 right

private def postSecondFiniteTable : FiniteTable where
  order := 7
  mul := postSecondFiniteMul
  assoc := by decide

private def PostSecondState.toFin : PostSecondState → Fin 7
  | .neutral => 0
  | .selected => 1
  | .protector => 2
  | .terminator => 3
  | .directTail => 4
  | .zero => 5
  | .two => 6

private def postSecondStateEmbedding :
    Embedding postSecondSemigroup postSecondFiniteTable.semigroup where
  toFun := PostSecondState.toFin
  map_mul := by
    intro left right
    cases left <;> cases right <;> rfl
  injective := by
    intro left right
    cases left <;> cases right <;> simp_all [PostSecondState.toFin]

set_option maxHeartbeats 0 in
private theorem postSecondFiniteModels :
    Models postSecondFiniteTable.semigroup basis :=
  models_of_finite_checks postSecondFiniteTable (by decide)

theorem postSecondModels : Models postSecondSemigroup basis := by
  intro identity member
  exact postSecondStateEmbedding.pullback_identity identity
    (postSecondFiniteModels identity member)

private def markerState : MarkerLetter → PostSecondState
  | .neutral => .neutral
  | .selected => .selected
  | .protector => .protector
  | .terminator => .terminator

private theorem step_eq_mul
    (state : PostSecondState) (letter : MarkerLetter) :
    state.step letter = state.mul (markerState letter) := by
  cases state <;> cases letter <;> rfl

private theorem fold_step_eq_fold_mul
    (selected protector : Nat) (terminator : Option Nat) :
    ∀ (letters : List Nat) (state : PostSecondState),
      letters.foldl
          (fun current letter =>
            current.step
              (markerLetter selected protector terminator letter)) state =
        letters.foldl
          (fun current letter =>
            current.mul
              (markerState
                (markerLetter selected protector terminator letter))) state
  | [], _ => rfl
  | letter :: rest, state => by
      simp only [List.foldl_cons, step_eq_mul]

private theorem postSecondState_eq_eval
    (word : Word Nat) (selected protector : Nat)
    (terminator : Option Nat) :
    postSecondState word selected protector terminator =
      postSecondSemigroup.eval
        (fun letter =>
          markerState
            (markerLetter selected protector terminator letter)) word := by
  cases word with
  | mk head tail =>
      simp only [postSecondState, postSecondStateList, Word.toList,
        List.foldl_cons, Semigroup.eval]
      rw [step_eq_mul]
      simp only [PostSecondState.mul]
      exact fold_step_eq_fold_mul selected protector terminator tail _

private theorem s5_870ModelsBasis :
    Models S5_870.table.semigroup basis :=
  models_of_finite_checks S5_870.table (by decide)

/-- Every genuine B15 derivation preserves the old gap data and the full
post-second state. This direction uses no completeness claim. -/
theorem refinedGapSignature_eq_of_derives
    {left right : Word Nat}
    (derivation : Derives basis left right) :
    refinedGapSignature left = refinedGapSignature right := by
  apply RefinedGapSignature.ext
  · let identity : Identity Nat := ⟨left, right⟩
    apply S5_870.valid_gapSignature_eq identity
    intro valuation
    exact derivation.sound s5_870ModelsBasis valuation
  · funext selected protector terminator
    change postSecondState left selected protector terminator =
      postSecondState right selected protector terminator
    rw [postSecondState_eq_eval, postSecondState_eq_eval]
    exact derivation.sound postSecondModels
      (fun letter =>
        markerState
          (markerLetter selected protector terminator letter))

end SemigroupBasis.CoRoots.Order6PublishedMonoid15

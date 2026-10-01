import SemigroupBasis.CoRoots.S5_831
import SemigroupBasis.Examples.LeftRegularBandThree

namespace SemigroupBasis.CoRoots.S5_831

open SemigroupBasis
open SemigroupBasis.Examples

/-- One first-occurrence phase. `doubled = false` records a boundary gap of
one; `doubled = true` records a boundary gap of at least two. -/
structure Phase where
  label : Nat
  doubled : Bool
deriving Repr, DecidableEq

def Phase.exponent (phase : Phase) : Nat :=
  if phase.doubled then 2 else 1

theorem Phase.exponent_eq_one_or_two (phase : Phase) :
    phase.exponent = 1 ∨ phase.exponent = 2 := by
  cases phase.doubled <;> simp [Phase.exponent]

def phaseLabels (phases : List Phase) : List Nat :=
  phases.map Phase.label

def phaseExponents (phases : List Phase) : List Nat :=
  phases.map Phase.exponent

def renderPhase (phase : Phase) : List Nat :=
  if phase.doubled then
    [phase.label, phase.label]
  else
    [phase.label]

def renderPhases (phases : List Phase) : List Nat :=
  phases.flatMap renderPhase

def markLastDoubled : List Phase → List Phase
  | [] => []
  | phase :: rest =>
      match rest with
      | [] => [⟨phase.label, true⟩]
      | next :: tail =>
          phase :: markLastDoubled (next :: tail)

/-- Reading an old letter only changes the current phase bit to two.
Reading a fresh letter starts a new singleton phase. -/
def phaseStep (phases : List Phase) (letter : Nat) : List Phase :=
  if letter ∈ phaseLabels phases then
    markLastDoubled phases
  else
    phases ++ [⟨letter, false⟩]

def scanPhases : List Phase → List Nat → List Phase
  | phases, [] => phases
  | phases, letter :: rest =>
      scanPhases (phaseStep phases letter) rest

/-- The scanner form of the positional profile. Starting positions are the
first occurrences. Each subsequent letter before the next first occurrence
sets the current gap bit to two; the final word boundary closes the last
phase. -/
def phaseProfileList : List Nat → List Phase
  | [] => []
  | head :: tail =>
      scanPhases [⟨head, false⟩] tail

def phaseProfile (word : Word Nat) : List Phase :=
  phaseProfileList word.toList

def phaseWord (phase : Phase) : Word Nat :=
  if phase.doubled then
    ⟨phase.label, [phase.label]⟩
  else
    Word.singleton phase.label

def profileWord : Phase → List Phase → Word Nat
  | phase, [] => phaseWord phase
  | phase, next :: rest =>
      phaseWord phase ++ profileWord next rest

def profileWordOr (fallback : Nat) : List Phase → Word Nat
  | [] => Word.singleton fallback
  | phase :: rest => profileWord phase rest

def canonicalList (word : Word Nat) : List Nat :=
  renderPhases (phaseProfile word)

/-- The canonical word `a1^e1 ... ak^ek`, with distinct phase labels and
all exponents in `{1, 2}`. -/
def canonicalWord (word : Word Nat) : Word Nat :=
  profileWordOr word.head (phaseProfile word)

theorem renderPhase_ne_nil (phase : Phase) :
    renderPhase phase ≠ [] := by
  cases phase with
  | mk label doubled =>
      cases doubled <;> simp [renderPhase]

theorem renderPhases_ne_nil
    {phases : List Phase} (nonempty : phases ≠ []) :
    renderPhases phases ≠ [] := by
  cases phases with
  | nil =>
      exact (nonempty rfl).elim
  | cons phase rest =>
      intro renderedEmpty
      have phaseEmpty : renderPhase phase = [] :=
        (List.append_eq_nil_iff.mp renderedEmpty).1
      exact renderPhase_ne_nil phase phaseEmpty

theorem phaseStep_ne_nil
    {phases : List Phase} (nonempty : phases ≠ [])
    (letter : Nat) :
    phaseStep phases letter ≠ [] := by
  unfold phaseStep
  split
  · induction phases with
    | nil =>
        exact (nonempty rfl).elim
    | cons phase rest ih =>
        cases rest with
        | nil =>
            simp [markLastDoubled]
        | cons next tail =>
            simp [markLastDoubled]
  · intro equal
    have := List.append_eq_nil_iff.mp equal
    exact nonempty this.1

theorem scanPhases_ne_nil
    {phases : List Phase} (nonempty : phases ≠ []) :
    ∀ letters, scanPhases phases letters ≠ []
  | [] => nonempty
  | letter :: rest =>
      scanPhases_ne_nil (phaseStep_ne_nil nonempty letter) rest

theorem phaseProfile_ne_nil (word : Word Nat) :
    phaseProfile word ≠ [] := by
  cases word with
  | mk head tail =>
      exact scanPhases_ne_nil (by simp) tail

@[simp]
theorem toList_phaseWord (phase : Phase) :
    (phaseWord phase).toList = renderPhase phase := by
  cases phase with
  | mk label doubled =>
      cases doubled <;> rfl

theorem toList_profileWord (phase : Phase) :
    ∀ rest,
      (profileWord phase rest).toList =
        renderPhases (phase :: rest)
  | [] => by
      simp [profileWord, renderPhases]
  | next :: tail => by
      rw [profileWord, Word.toList_append,
        toList_phaseWord, toList_profileWord]
      rfl

@[simp]
theorem toList_canonicalWord (word : Word Nat) :
    (canonicalWord word).toList = canonicalList word := by
  unfold canonicalWord canonicalList
  cases profileShape : phaseProfile word with
  | nil =>
      exact False.elim (phaseProfile_ne_nil word profileShape)
  | cons phase rest =>
      exact toList_profileWord phase rest

theorem profileWordOr_eq_of_ne_nil
    (leftFallback rightFallback : Nat)
    {phases : List Phase} (nonempty : phases ≠ []) :
    profileWordOr leftFallback phases =
      profileWordOr rightFallback phases := by
  cases phases with
  | nil =>
      exact (nonempty rfl).elim
  | cons phase rest =>
      rfl

theorem phaseLabels_markLastDoubled :
    ∀ phases,
      phaseLabels (markLastDoubled phases) =
        phaseLabels phases
  | [] => rfl
  | phase :: rest => by
      cases rest with
      | nil =>
          rfl
      | cons next tail =>
          change
            phase.label ::
                phaseLabels (markLastDoubled (next :: tail)) =
              phase.label :: phaseLabels (next :: tail)
          rw [phaseLabels_markLastDoubled]

theorem phaseLabels_phaseStep
    (phases : List Phase) (letter : Nat) :
    phaseLabels (phaseStep phases letter) =
      if letter ∈ phaseLabels phases then
        phaseLabels phases
      else
        phaseLabels phases ++ [letter] := by
  by_cases member : letter ∈ phaseLabels phases
  · simp [phaseStep, member, phaseLabels_markLastDoubled]
  · have stepEq :
        phaseStep phases letter =
          phases ++ [⟨letter, false⟩] := by
      simp [phaseStep, member]
    rw [stepEq, if_neg member]
    simp [phaseLabels]

private theorem nodup_append_singleton
    {letters : List Nat} {letter : Nat}
    (nodup : letters.Nodup) (absent : letter ∉ letters) :
    (letters ++ [letter]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨nodup, by simp, ?_⟩
  intro left leftMember right rightMember equal
  have rightEq : right = letter := by
    simpa using rightMember
  subst right
  subst left
  exact absent leftMember

theorem phaseLabels_scanPhases_nodup
    {phases : List Phase}
    (nodup : (phaseLabels phases).Nodup) :
    ∀ letters,
      (phaseLabels (scanPhases phases letters)).Nodup
  | [] => nodup
  | letter :: rest => by
      have stepNodup :
          (phaseLabels (phaseStep phases letter)).Nodup := by
        rw [phaseLabels_phaseStep]
        by_cases member : letter ∈ phaseLabels phases
        · rw [if_pos member]
          exact nodup
        · rw [if_neg member]
          exact nodup_append_singleton nodup member
      exact phaseLabels_scanPhases_nodup stepNodup rest

theorem phaseLabels_phaseProfile_nodup (word : Word Nat) :
    (phaseLabels (phaseProfile word)).Nodup := by
  cases word with
  | mk head tail =>
      apply phaseLabels_scanPhases_nodup
      simp [phaseLabels]

theorem mem_phaseExponents_phaseProfile
    (word : Word Nat) {exponent : Nat}
    (member :
      exponent ∈ phaseExponents (phaseProfile word)) :
    exponent = 1 ∨ exponent = 2 := by
  rcases List.mem_map.mp member with
    ⟨phase, _, rfl⟩
  exact Phase.exponent_eq_one_or_two phase

theorem mem_renderPhases_iff (letter : Nat) :
    ∀ phases,
      letter ∈ renderPhases phases ↔
        letter ∈ phaseLabels phases
  | [] => by
      simp [renderPhases, phaseLabels]
  | phase :: rest => by
      cases phase with
      | mk label doubled =>
          rw [renderPhases, List.flatMap_cons,
            List.mem_append, phaseLabels, List.map_cons,
            List.mem_cons]
          change
            (letter ∈ renderPhase ⟨label, doubled⟩ ∨
                letter ∈ renderPhases rest) ↔
              letter = label ∨ letter ∈ phaseLabels rest
          rw [mem_renderPhases_iff letter rest]
          cases doubled <;> simp [renderPhase]

private theorem filter_ne_eq_self_of_not_mem
    (selected : Nat) {letters : List Nat}
    (absent : selected ∉ letters) :
    letters.filter (fun letter => decide (letter ≠ selected)) =
      letters := by
  apply List.filter_eq_self.mpr
  intro letter member
  exact decide_eq_true <| by
    intro equal
    subst letter
    exact absent member

/-- Rendering a nodup phase list and then taking first occurrences recovers
the phase labels literally. -/
theorem firstOccurrenceSequence_renderPhases
    {phases : List Phase}
    (nodup : (phaseLabels phases).Nodup) :
    firstOccurrenceSequence (renderPhases phases) =
      phaseLabels phases := by
  induction phases with
  | nil =>
      rfl
  | cons phase rest ih =>
      cases phase with
      | mk label doubled =>
          have data :
              label ∉ phaseLabels rest ∧
                (phaseLabels rest).Nodup :=
            List.nodup_cons.mp nodup
          have restNormal := ih data.2
          have kept :=
            filter_ne_eq_self_of_not_mem label data.1
          have absentSymm :
              ∀ next, next ∈ phaseLabels rest → next ≠ label := by
            intro next member equal
            subst next
            exact data.1 member
          cases doubled with
          | false =>
              change
                firstOccurrenceSequence
                    (label :: renderPhases rest) =
                  label :: phaseLabels rest
              simp only [firstOccurrenceSequence]
              rw [restNormal, kept]
          | true =>
              change
                firstOccurrenceSequence
                    (label :: label :: renderPhases rest) =
                  label :: phaseLabels rest
              simp only [firstOccurrenceSequence]
              rw [restNormal, kept]
              simp
              exact absentSymm

/-- Equality of the complete phase occupancy invariant. -/
def SamePhaseOccupancySignature
    (left right : Word Nat) : Prop :=
  phaseProfile left = phaseProfile right

namespace SamePhaseOccupancySignature

theorem refl (word : Word Nat) :
    SamePhaseOccupancySignature word word :=
  rfl

theorem symm {left right : Word Nat}
    (same : SamePhaseOccupancySignature left right) :
    SamePhaseOccupancySignature right left :=
  Eq.symm same

theorem trans {left middle right : Word Nat}
    (first : SamePhaseOccupancySignature left middle)
    (second : SamePhaseOccupancySignature middle right) :
    SamePhaseOccupancySignature left right :=
  Eq.trans first second

theorem canonicalWord_eq {left right : Word Nat}
    (same : SamePhaseOccupancySignature left right) :
    canonicalWord left = canonicalWord right := by
  apply Word.toList_injective
  simp only [toList_canonicalWord, canonicalList]
  rw [same]

end SamePhaseOccupancySignature

end SemigroupBasis.CoRoots.S5_831

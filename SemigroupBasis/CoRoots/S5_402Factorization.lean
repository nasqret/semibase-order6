import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_402Normalization

namespace SemigroupBasis.CoRoots.S5_402

open SemigroupBasis

abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-! ## Gathering arbitrary repeated occurrences into local squares -/

/-- Duplicate the left occurrence of a displayed repeated letter. -/
theorem listDerivesExpandLeftOccurrence
    (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([letter] ++ middle ++ [letter])
        ([letter, letter] ++ middle ++ [letter])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (S5_107.ListDerives.ofWord <|
          derivesPowerExpansion (Word.singleton letter))
  | head :: tail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (S5_107.ListDerives.ofWord <|
            derivesLeftDuplication
              (Word.singleton letter)
              (listWordOfCons head tail))

/-- Duplicate the right occurrence of a displayed repeated letter. -/
theorem listDerivesExpandRightOccurrence
    (letter : Nat) :
    ∀ middle : List Nat,
      ListDerives
        ([letter] ++ middle ++ [letter])
        ([letter] ++ middle ++ [letter, letter])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (S5_107.ListDerives.ofWord <|
          derivesPowerExpansion (Word.singleton letter))
  | head :: tail => by
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (S5_107.ListDerives.ofWord <|
            derivesRightDuplication
              (Word.singleton letter)
              (listWordOfCons head tail))

/-- Duplicate one selected occurrence of a globally repeated letter. The
other occurrence may lie on either side of the selected position. -/
theorem listDerivesDuplicateSelectedOccurrence
    (letter : Nat) (before after : List Nat)
    (multiple :
      2 ≤ (before ++ [letter] ++ after).count letter) :
    ListDerives
      (before ++ [letter] ++ after)
      (before ++ [letter, letter] ++ after) := by
  by_cases afterMember : letter ∈ after
  · obtain ⟨middle, suffix, split⟩ :=
      List.mem_iff_append.mp afterMember
    have expanded :=
      (listDerivesExpandLeftOccurrence letter middle).context
        before suffix
    simpa [split, List.append_assoc] using expanded
  · have beforeMember : letter ∈ before := by
      apply Classical.byContradiction
      intro beforeAbsent
      have beforeZero : before.count letter = 0 :=
        List.count_eq_zero.mpr beforeAbsent
      have afterZero : after.count letter = 0 :=
        List.count_eq_zero.mpr afterMember
      have countOne :
          (before ++ [letter] ++ after).count letter = 1 := by
        simp [List.count_append, beforeZero, afterZero]
      rw [countOne] at multiple
      omega
    obtain ⟨beforePrefix, middle, split⟩ :=
      List.mem_iff_append.mp beforeMember
    have expanded :=
      (listDerivesExpandRightOccurrence letter middle).context
        beforePrefix after
    simpa [split, List.append_assoc] using expanded

/-! ## Literal simple-block/repeated-marker factorization -/

/-- Scan a list into maximal blocks of globally simple letters, each
terminated by one globally repeated marker, plus the trailing simple block.
The current block is stored in reverse order while scanning. -/
def terminatedBlockScan
    (whole current : List Nat) :
    List Nat → List (List Nat × Nat) × List Nat
  | [] => ([], current.reverse)
  | letter :: rest =>
      if whole.count letter = 1 then
        terminatedBlockScan whole (letter :: current) rest
      else
        let scanned := terminatedBlockScan whole [] rest
        ((current.reverse, letter) :: scanned.1, scanned.2)

/-- Render each simple block followed by its repeated marker. -/
def renderTerminatedBlocks :
    List (List Nat × Nat) → List Nat
  | [] => []
  | (block, marker) :: rest =>
      block ++ marker :: renderTerminatedBlocks rest

@[simp]
theorem renderTerminatedBlocks_append
    (left right : List (List Nat × Nat)) :
    renderTerminatedBlocks (left ++ right) =
      renderTerminatedBlocks left ++ renderTerminatedBlocks right := by
  induction left with
  | nil =>
      rfl
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      simp [renderTerminatedBlocks, ih, List.append_assoc]

/-- Render each simple block followed by a local square of its marker. -/
def renderSquaredTerminatedBlocks :
    List (List Nat × Nat) → List Nat
  | [] => []
  | (block, marker) :: rest =>
      block ++ marker :: marker ::
        renderSquaredTerminatedBlocks rest

@[simp]
theorem renderSquaredTerminatedBlocks_append
    (left right : List (List Nat × Nat)) :
    renderSquaredTerminatedBlocks (left ++ right) =
      renderSquaredTerminatedBlocks left ++
        renderSquaredTerminatedBlocks right := by
  induction left with
  | nil =>
      rfl
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      simp [renderSquaredTerminatedBlocks, ih,
        List.append_assoc]

/-- Marker projection of a terminated factor list, retaining occurrences. -/
def terminatedFactorMarkers
    (factors : List (List Nat × Nat)) : List Nat :=
  factors.map fun factor => factor.2

/-- The complete terminated-factor list of a word list. -/
def terminatedBlocks (letters : List Nat) :
    List (List Nat × Nat) :=
  (terminatedBlockScan letters [] letters).1

/-- The trailing globally simple block after the final repeated marker. -/
def terminatedFinalBlock (letters : List Nat) : List Nat :=
  (terminatedBlockScan letters [] letters).2

/-- The scanner is a literal factorization of the unprocessed suffix. -/
theorem terminatedBlockScan_render
    (whole current remaining : List Nat) :
    renderTerminatedBlocks
        (terminatedBlockScan whole current remaining).1 ++
      (terminatedBlockScan whole current remaining).2 =
        current.reverse ++ remaining := by
  induction remaining generalizing current with
  | nil =>
      simp [terminatedBlockScan, renderTerminatedBlocks]
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · simpa [terminatedBlockScan, simple, List.reverse_cons,
          List.append_assoc] using ih (letter :: current)
      · have tail := ih ([] : List Nat)
        simpa [terminatedBlockScan, simple, renderTerminatedBlocks,
          List.append_assoc] using tail

/-- Every list is exactly its rendered factors followed by its trailing
simple block. -/
theorem terminatedBlocks_render (letters : List Nat) :
    renderTerminatedBlocks (terminatedBlocks letters) ++
      terminatedFinalBlock letters = letters := by
  simpa [terminatedBlocks, terminatedFinalBlock] using
    terminatedBlockScan_render letters [] letters

/-- Every emitted marker is globally non-simple in the frozen whole list. -/
theorem terminatedBlockScan_marker_not_simple
    (whole current remaining : List Nat) :
    ∀ factor ∈ (terminatedBlockScan whole current remaining).1,
      whole.count factor.2 ≠ 1 := by
  induction remaining generalizing current with
  | nil =>
      simp [terminatedBlockScan]
  | cons letter rest ih =>
      by_cases simple : whole.count letter = 1
      · simpa [terminatedBlockScan, simple] using
          ih (letter :: current)
      · intro factor member
        simp only [terminatedBlockScan, if_neg simple,
          List.mem_cons] at member
        rcases member with rfl | member
        · exact simple
        · exact ih ([] : List Nat) factor member

/-- If the current accumulator is globally simple, every emitted block and
the final suffix contain only globally simple letters. -/
theorem terminatedBlockScan_blocks_simple
    (whole current remaining : List Nat)
    (currentSimple :
      ∀ letter ∈ current, whole.count letter = 1) :
    (∀ factor ∈ (terminatedBlockScan whole current remaining).1,
        ∀ letter ∈ factor.1, whole.count letter = 1) ∧
      (∀ letter ∈ (terminatedBlockScan whole current remaining).2,
        whole.count letter = 1) := by
  induction remaining generalizing current with
  | nil =>
      constructor
      · simp [terminatedBlockScan]
      · intro letter member
        change letter ∈ current.reverse at member
        exact currentSimple letter <| by
          simpa using member
  | cons next rest ih =>
      by_cases simple : whole.count next = 1
      · have extendedSimple :
            ∀ letter ∈ next :: current,
              whole.count letter = 1 := by
          intro letter member
          simp only [List.mem_cons] at member
          rcases member with equal | member
          · simpa [equal] using simple
          · exact currentSimple letter member
        simpa [terminatedBlockScan, simple] using
          ih (next :: current) extendedSimple
      · have tail :=
          ih ([] : List Nat) (by simp)
        constructor
        · intro factor member letter letterMember
          simp only [terminatedBlockScan, if_neg simple,
            List.mem_cons] at member
          rcases member with rfl | member
          · exact currentSimple letter <| by
              simpa using letterMember
          · exact tail.1 factor member letter letterMember
        · simpa [terminatedBlockScan, simple] using tail.2

/-- A factor marker occurs in the literal rendering. -/
theorem marker_mem_renderTerminatedBlocks
    {factors : List (List Nat × Nat)}
    {factor : List Nat × Nat}
    (member : factor ∈ factors) :
    factor.2 ∈ renderTerminatedBlocks factors := by
  induction factors with
  | nil =>
      simp at member
  | cons first rest ih =>
      rcases first with ⟨block, marker⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [renderTerminatedBlocks]
      · simp only [renderTerminatedBlocks, List.mem_append,
          List.mem_cons]
        exact Or.inr (Or.inr (ih member))

/-- Every public marker occurs at least twice in the original list. -/
theorem terminatedBlocks_marker_multiple
    (letters : List Nat)
    (factor : List Nat × Nat)
    (member : factor ∈ terminatedBlocks letters) :
    2 ≤ letters.count factor.2 := by
  have markerInRendering :
      factor.2 ∈ renderTerminatedBlocks (terminatedBlocks letters) :=
    marker_mem_renderTerminatedBlocks member
  have markerInLetters : factor.2 ∈ letters := by
    rw [← terminatedBlocks_render letters]
    exact List.mem_append_left _ markerInRendering
  have positive : 0 < letters.count factor.2 :=
    List.count_pos_iff.mpr markerInLetters
  have notSimple :=
    terminatedBlockScan_marker_not_simple
      letters [] letters factor member
  omega

/-- Every factor block consists entirely of globally simple letters. -/
theorem terminatedBlocks_block_simple
    (letters : List Nat)
    (factor : List Nat × Nat)
    (factorMember : factor ∈ terminatedBlocks letters)
    (letter : Nat)
    (letterMember : letter ∈ factor.1) :
    letters.count letter = 1 := by
  exact
    (terminatedBlockScan_blocks_simple
      letters [] letters (by simp)).1
        factor factorMember letter letterMember

/-- Every letter in the trailing block is globally simple. -/
theorem terminatedFinalBlock_letter_simple
    (letters : List Nat)
    (letter : Nat)
    (member : letter ∈ terminatedFinalBlock letters) :
    letters.count letter = 1 := by
  exact
    (terminatedBlockScan_blocks_simple
      letters [] letters (by simp)).2 letter member

/-- Duplicating a selected occurrence never decreases any tested count. -/
theorem count_le_count_duplicateSelected
    (tested inserted : Nat)
    (before after : List Nat) :
    (before ++ [inserted] ++ after).count tested ≤
      (before ++ [inserted, inserted] ++ after).count tested := by
  by_cases equality : tested = inserted
  · subst inserted
    simp [List.count_append]
  · have reverseEquality : inserted ≠ tested :=
      Ne.symm equality
    simp [List.count_append, equality, reverseEquality]

/-- Square every emitted marker while retaining an arbitrary processed
prefix. The witness for repetition may occur on either side of the selected
marker, so this handles arbitrary scattered occurrences. -/
theorem listDerivesSquareTerminatedMarkersAux
    (final : List Nat) :
    ∀ (factors : List (List Nat × Nat))
      (before : List Nat),
      (∀ factor ∈ factors,
        2 ≤
          (before ++
            renderTerminatedBlocks factors ++ final).count factor.2) →
      ListDerives
        (before ++ renderTerminatedBlocks factors ++ final)
        (before ++ renderSquaredTerminatedBlocks factors ++ final)
  | [], before, _ => by
      simpa [renderTerminatedBlocks,
        renderSquaredTerminatedBlocks] using
          (S5_107.ListDerives.refl (basis := basis) (before ++ final))
  | (block, marker) :: rest, before, multiples => by
      have markerMultiple :
          2 ≤
            ((before ++ block) ++ [marker] ++
              (renderTerminatedBlocks rest ++ final)).count marker := by
        simpa [renderTerminatedBlocks, List.append_assoc] using
          multiples (block, marker) (by simp)
      have firstRaw :=
        listDerivesDuplicateSelectedOccurrence
          marker (before ++ block)
          (renderTerminatedBlocks rest ++ final)
          markerMultiple
      have firstStep :
          ListDerives
            (before ++
              renderTerminatedBlocks
                ((block, marker) :: rest) ++ final)
            ((before ++ block ++ [marker, marker]) ++
              renderTerminatedBlocks rest ++ final) := by
        simpa [renderTerminatedBlocks,
          List.append_assoc] using firstRaw
      have restMultiples :
          ∀ factor ∈ rest,
            2 ≤
              ((before ++ block ++ [marker, marker]) ++
                renderTerminatedBlocks rest ++ final).count
                  factor.2 := by
        intro factor member
        have oldMultiple :
            2 ≤
              ((before ++ block) ++ [marker] ++
                (renderTerminatedBlocks rest ++ final)).count
                  factor.2 := by
          simpa [renderTerminatedBlocks,
            List.append_assoc] using
              multiples factor (by simp [member])
        have monotone :=
          count_le_count_duplicateSelected
            factor.2 marker (before ++ block)
              (renderTerminatedBlocks rest ++ final)
        have newMultiple :=
          Nat.le_trans oldMultiple monotone
        simpa [List.append_assoc] using newMultiple
      have restStep :=
        listDerivesSquareTerminatedMarkersAux
          final rest
          (before ++ block ++ [marker, marker])
          restMultiples
      have restStep' :
          ListDerives
            ((before ++ block ++ [marker, marker]) ++
              renderTerminatedBlocks rest ++ final)
            ((before ++ block ++ [marker, marker]) ++
              renderSquaredTerminatedBlocks rest ++ final) := by
        simpa [List.append_assoc] using restStep
      have combined := firstStep.trans restStep'
      simpa [renderSquaredTerminatedBlocks,
        List.append_assoc] using combined

/-- Every word list derives to a grouped factorization in which each
globally repeated occurrence is represented by a local square, while every
globally simple block remains literal. -/
theorem listDerivesSquareAllTerminatedMarkers
    (letters : List Nat) :
    ListDerives letters
      (renderSquaredTerminatedBlocks
          (terminatedBlocks letters) ++
        terminatedFinalBlock letters) := by
  have multiples :
      ∀ factor ∈ terminatedBlocks letters,
        2 ≤
          (renderTerminatedBlocks
              (terminatedBlocks letters) ++
            terminatedFinalBlock letters).count factor.2 := by
    intro factor member
    rw [terminatedBlocks_render letters]
    exact
      terminatedBlocks_marker_multiple
        letters factor member
  have squared :=
    listDerivesSquareTerminatedMarkersAux
      (terminatedFinalBlock letters)
      (terminatedBlocks letters) [] <| by
        simpa using multiples
  simpa [terminatedBlocks_render letters] using squared

end SemigroupBasis.CoRoots.S5_402

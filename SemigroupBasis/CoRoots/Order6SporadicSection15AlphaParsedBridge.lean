import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaOccurrencePairing
import SemigroupBasis.CoRoots.Order6SporadicSection15BranchFacts
import SemigroupBasis.CoRoots.Order6SporadicSection15ParsedWords

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace AlphaParsedBridge

/-! ## Connecting terminated factors to alpha occurrence pairing

The terminated parser already isolates every globally nonsimple occurrence as
a factor marker.  This file views those markers as the positional labels used
by `AlphaOccurrencePairing.renderMarkerGaps`: the first factor block remains a
prefix, and each marker is followed by the next factor block or by the final
parser block.

Only occurrence pairing is performed here.  The parsed factors and gaps stay
in source order; no sorting, gap compaction, or alpha normalization is claimed.
-/

/-- Marker occurrences projected from the terminated factors, in source
order. -/
def markerLabels (letters : List Nat) : List Nat :=
  S5_107.terminatedFactorMarkers (ParsedWords.factors letters)

/-- The gap after each parsed marker.  A marker before another factor receives
that factor's simple block; the final marker receives the parser's final
block. -/
def postMarkerGaps (letters : List Nat) : List (List Nat) :=
  match ParsedWords.factors letters with
  | [] => []
  | _ :: rest =>
      S5_107.terminatedFactorBlocks rest ++
        [ParsedWords.finalBlock letters]

/-- The literal prefix carried by the terminated decomposition.  The empty
factor fallback is the complete final block. -/
def initialBlock (letters : List Nat) : List Nat :=
  match ParsedWords.factors letters with
  | [] => ParsedWords.finalBlock letters
  | first :: _ => first.1

/-- There is exactly one post-marker gap for every parsed marker. -/
theorem postMarkerGaps_length_eq_markerLabels_length
    (letters : List Nat) :
    (postMarkerGaps letters).length =
      (markerLabels letters).length := by
  cases shape : ParsedWords.factors letters with
  | nil =>
      simp [postMarkerGaps, markerLabels, shape,
        S5_107.terminatedFactorMarkers]
  | cons first rest =>
      simp [postMarkerGaps, markerLabels, shape,
        S5_107.terminatedFactorBlocks,
        S5_107.terminatedFactorMarkers]

private theorem renderFactors_cons_eq_initial_render
    (first : ParsedWords.Factor)
    (rest : List ParsedWords.Factor)
    (final : List Nat) :
    ParsedWords.renderFactors (first :: rest) ++ final =
      first.1 ++
        AlphaOccurrencePairing.renderMarkerGaps
          (S5_107.terminatedFactorMarkers (first :: rest))
          (S5_107.terminatedFactorBlocks rest ++ [final]) := by
  induction rest generalizing first with
  | nil =>
      rcases first with ⟨block, marker⟩
      simp [ParsedWords.renderFactors,
        S5_107.renderTerminatedBlocks,
        S5_107.terminatedFactorBlocks,
        S5_107.terminatedFactorMarkers,
        AlphaOccurrencePairing.renderMarkerGaps]
  | cons next rest induction =>
      rcases first with ⟨block, marker⟩
      rcases next with ⟨nextBlock, nextMarker⟩
      have tailRendered := induction (nextBlock, nextMarker)
      simp [ParsedWords.renderFactors,
        S5_107.renderTerminatedBlocks,
        S5_107.terminatedFactorBlocks,
        S5_107.terminatedFactorMarkers,
        AlphaOccurrencePairing.renderMarkerGaps,
        List.append_assoc] at tailRendered ⊢
      exact tailRendered

/-- The marker-gap rendering is literally the source list after its parsed
initial block. -/
theorem reconstruct (letters : List Nat) :
    initialBlock letters ++
        AlphaOccurrencePairing.renderMarkerGaps
          (markerLabels letters) (postMarkerGaps letters) =
      letters := by
  cases shape : ParsedWords.factors letters with
  | nil =>
      have literal := ParsedWords.reconstruct letters
      rw [shape] at literal
      simpa [initialBlock, markerLabels, postMarkerGaps, shape,
        ParsedWords.renderFactors,
        S5_107.renderTerminatedBlocks,
        S5_107.terminatedFactorMarkers,
        AlphaOccurrencePairing.renderMarkerGaps] using literal
  | cons first rest =>
      have rendered :=
        renderFactors_cons_eq_initial_render
          first rest (ParsedWords.finalBlock letters)
      have literal := ParsedWords.reconstruct letters
      rw [shape] at literal
      simpa [initialBlock, markerLabels, postMarkerGaps, shape] using
        rendered.symm.trans literal

/-- A nonempty parsed decomposition uses the scanner's actual initial simple
block as its literal prefix. -/
theorem initialBlock_eq_initialSimpleBlock_of_factors_cons
    (letters : List Nat)
    (first : ParsedWords.Factor)
    (rest : List ParsedWords.Factor)
    (shape : ParsedWords.factors letters = first :: rest) :
    initialBlock letters = S5_107.initialSimpleBlock letters := by
  simpa [initialBlock, shape] using
    ParsedWords.firstBlock_eq_initialSimpleBlock
      letters first rest shape

/-- The alpha branch contains a doubled label, so its terminated factor list
cannot be empty. -/
theorem factors_ne_nil_of_branch_alpha
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    ParsedWords.factors letters ≠ [] := by
  obtain ⟨marker, markerCount⟩ :=
    CanonicalData.exists_count_eq_two_of_branch_alpha branch
  have markerMember : marker ∈ markerLabels letters := by
    simpa [markerLabels, ParsedWords.factors] using
      (S5_107.mem_terminatedFactorMarkers_iff marker letters).2
        (by omega)
  intro factorsEmpty
  simp [markerLabels, factorsEmpty,
    S5_107.terminatedFactorMarkers] at markerMember

/-- On the alpha branch, the final parser block is the last post-marker gap;
all preceding gaps come from the internal terminated factors. -/
theorem exists_internal_postMarkerGaps_of_branch_alpha
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    Exists fun internal : List (List Nat) =>
      postMarkerGaps letters =
        internal ++ [ParsedWords.finalBlock letters] := by
  have factorsNe := factors_ne_nil_of_branch_alpha branch
  cases shape : ParsedWords.factors letters with
  | nil => exact absurd shape factorsNe
  | cons first rest =>
      refine ⟨S5_107.terminatedFactorBlocks rest, ?_⟩
      simp [postMarkerGaps, shape]

/-- On the alpha branch the literal parsed prefix is the established initial
simple block. -/
theorem initialBlock_eq_initialSimpleBlock_of_branch_alpha
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    initialBlock letters = S5_107.initialSimpleBlock letters := by
  obtain ⟨first, rest, shape⟩ :=
    List.exists_cons_of_ne_nil
      (factors_ne_nil_of_branch_alpha branch)
  exact
    initialBlock_eq_initialSimpleBlock_of_factors_cons
      letters first rest shape

/-- Alpha words are reconstructed literally as the initial simple block
followed by the alternating parsed marker-gap rendering. -/
theorem reconstruct_with_initialSimpleBlock_of_branch_alpha
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    S5_107.initialSimpleBlock letters ++
        AlphaOccurrencePairing.renderMarkerGaps
          (markerLabels letters) (postMarkerGaps letters) =
      letters := by
  rw [← initialBlock_eq_initialSimpleBlock_of_branch_alpha branch]
  exact reconstruct letters

/-- Every letter in a post-marker gap is globally simple in the source
list. -/
theorem postMarkerGap_letter_simple
    (letters : List Nat)
    (gap : List Nat)
    (gapMember : gap ∈ postMarkerGaps letters)
    (letter : Nat)
    (letterMember : letter ∈ gap) :
    letters.count letter = 1 := by
  cases shape : ParsedWords.factors letters with
  | nil =>
      simp [postMarkerGaps, shape] at gapMember
  | cons first rest =>
      have gapCases :
          gap ∈ S5_107.terminatedFactorBlocks rest ∨
            gap = ParsedWords.finalBlock letters := by
        simpa [postMarkerGaps, shape] using gapMember
      rcases gapCases with restMember | finalGap
      · change gap ∈ rest.map (fun factor => factor.1) at restMember
        rcases List.mem_map.mp restMember with
          ⟨factor, factorMember, factorBlock⟩
        have wholeMember : factor ∈ ParsedWords.factors letters := by
          rw [shape]
          exact List.Mem.tail first factorMember
        apply ParsedWords.factor_block_letter_simple
          letters factor wholeMember letter
        rw [factorBlock]
        exact letterMember
      · subst gap
        exact ParsedWords.finalBlock_letter_simple
          letters letter letterMember

/-- Parsed markers are absent from every parsed post-marker gap. -/
theorem markerFreeGaps (letters : List Nat) :
    AlphaOccurrencePairing.MarkerFreeGaps
      (markerLabels letters) (postMarkerGaps letters) := by
  intro marker markerMember gap gapMember markerInGap
  have multiple : 2 <= letters.count marker := by
    apply (S5_107.mem_terminatedFactorMarkers_iff marker letters).1
    simpa [markerLabels, ParsedWords.factors] using markerMember
  have simple :=
    postMarkerGap_letter_simple
      letters gap gapMember marker markerInGap
  omega

/-- Every parsed marker occurs exactly twice when the dispatcher selects the
alpha branch. -/
theorem twiceOccurringMarkers_of_branch_alpha
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    AlphaOccurrencePairing.TwiceOccurringMarkers
      (markerLabels letters) := by
  intro marker markerMember
  have multiple : 2 <= letters.count marker := by
    apply (S5_107.mem_terminatedFactorMarkers_iff marker letters).1
    simpa [markerLabels, ParsedWords.factors] using markerMember
  have upper :=
    CanonicalData.count_le_two_of_branch_alpha branch marker
  have sourceCount : letters.count marker = 2 := by
    omega
  calc
    (markerLabels letters).count marker = letters.count marker := by
      simpa [markerLabels, ParsedWords.factors] using
        S5_107.count_terminatedFactorMarkers_of_multiple
          marker letters multiple
    _ = 2 := sourceCount

/-- The paired marker projection is a list of adjacent equal pairs. -/
theorem pairedMarkerLabels_of_branch_alpha
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    AlphaOccurrencePairing.PairedMarkerList
      (AlphaOccurrencePairing.pairMarkerOccurrences
        (markerLabels letters)) :=
  AlphaOccurrencePairing.pairMarkerOccurrences_paired
    (markerLabels letters)
    (twiceOccurringMarkers_of_branch_alpha branch)

/-- Starting from the original alpha word, pair its raw parsed marker
occurrences while leaving the initial block and every post-marker gap fixed.
This is only the occurrence-pairing stage. -/
theorem listDerivesPairMarkerOccurrences_of_branch_alpha
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    ListDerives letters
      (S5_107.initialSimpleBlock letters ++
        AlphaOccurrencePairing.renderMarkerGaps
          (AlphaOccurrencePairing.pairMarkerOccurrences
            (markerLabels letters))
          (postMarkerGaps letters)) := by
  have paired :=
    AlphaOccurrencePairing.listDerivesPairMarkerOccurrences
      (S5_107.initialSimpleBlock letters) []
      (markerLabels letters) (postMarkerGaps letters)
      (postMarkerGaps_length_eq_markerLabels_length letters)
      (twiceOccurringMarkers_of_branch_alpha branch)
      (markerFreeGaps letters)
  rw [reconstruct_with_initialSimpleBlock_of_branch_alpha
    letters branch] at paired
  simpa only [List.append_nil] using paired

end AlphaParsedBridge

end SemigroupBasis.CoRoots.Order6SporadicSection15

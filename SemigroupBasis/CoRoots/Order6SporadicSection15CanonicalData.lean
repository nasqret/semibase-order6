import SemigroupBasis.CoRoots.S5_107MarkerCombinatorics

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis.CoRoots

namespace CanonicalData

/-! ## Globally simple letters and their maximal runs -/

/-- Retain, in their current order, the letters that occur exactly once in
the ambient list `whole`. -/
def simpleLetterProjection
    (whole letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (whole.count letter = 1)

/-- Maximal consecutive runs of letters that are globally simple. -/
def maximalSimpleRuns (letters : List Nat) : List (List Nat) :=
  S5_107.simpleBlocks letters

@[simp]
theorem simpleLetterProjection_nil (whole : List Nat) :
    simpleLetterProjection whole [] = [] :=
  rfl

theorem simpleLetterProjection_append
    (whole left right : List Nat) :
    simpleLetterProjection whole (left ++ right) =
      simpleLetterProjection whole left ++
        simpleLetterProjection whole right := by
  simp [simpleLetterProjection]

/-- The run scanner neither loses nor duplicates a globally simple letter. -/
theorem maximalSimpleRuns_flatten (letters : List Nat) :
    (maximalSimpleRuns letters).flatten =
      simpleLetterProjection letters letters := by
  simpa [maximalSimpleRuns, simpleLetterProjection] using
    S5_107.simpleBlocks_flatten letters

theorem maximalSimpleRuns_blocks_nonempty (letters : List Nat) :
    forall block, block ∈ maximalSimpleRuns letters -> block ≠ [] := by
  simpa [maximalSimpleRuns] using
    S5_107.simpleBlocks_blocks_nonempty letters

theorem maximalSimpleRuns_flatten_nodup (letters : List Nat) :
    (maximalSimpleRuns letters).flatten.Nodup := by
  simpa [maximalSimpleRuns] using
    S5_107.simpleBlocks_flatten_nodup letters

theorem maximalSimpleRuns_nodup (letters : List Nat) :
    (maximalSimpleRuns letters).Nodup := by
  simpa [maximalSimpleRuns] using
    S5_107.simpleBlocks_nodup letters

/-! ## Sorted multiplicity classes -/

/-- Letters occurring exactly twice, once each and in increasing order. -/
def sortedDoubledLetters (letters : List Nat) : List Nat :=
  (S5_107.sortedMultipleLetters letters).filter
    (fun letter => decide (letters.count letter = 2))

/-- Letters occurring at least three times, once each and in increasing
order. -/
def sortedHighCountLetters (letters : List Nat) : List Nat :=
  (S5_107.sortedMultipleLetters letters).filter
    (fun letter => decide (3 ≤ letters.count letter))

theorem sortedDoubledLetters_mem_iff
    (letter : Nat) (letters : List Nat) :
    letter ∈ sortedDoubledLetters letters ↔
      letters.count letter = 2 := by
  simp only [sortedDoubledLetters, List.mem_filter,
    S5_107.sortedMultipleLetters_mem_iff, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro doubled
    exact ⟨by omega, doubled⟩

theorem sortedHighCountLetters_mem_iff
    (letter : Nat) (letters : List Nat) :
    letter ∈ sortedHighCountLetters letters ↔
      3 ≤ letters.count letter := by
  simp only [sortedHighCountLetters, List.mem_filter,
    S5_107.sortedMultipleLetters_mem_iff, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro high
    exact ⟨by omega, high⟩

theorem sortedDoubledLetters_nodup (letters : List Nat) :
    (sortedDoubledLetters letters).Nodup := by
  exact (S5_107.sortedMultipleLetters_nodup letters).filter _

theorem sortedHighCountLetters_nodup (letters : List Nat) :
    (sortedHighCountLetters letters).Nodup := by
  exact (S5_107.sortedMultipleLetters_nodup letters).filter _

theorem sortedDoubledLetters_pairwise (letters : List Nat) :
    (sortedDoubledLetters letters).Pairwise (· ≤ ·) := by
  exact (S5_107.sortedMultipleLetters_pairwise letters).filter _

theorem sortedHighCountLetters_pairwise (letters : List Nat) :
    (sortedHighCountLetters letters).Pairwise (· ≤ ·) := by
  exact (S5_107.sortedMultipleLetters_pairwise letters).filter _

theorem sortedMultiplicityClasses_mem_iff
    (letter : Nat) (letters : List Nat) :
    letter ∈ sortedDoubledLetters letters ∨
        letter ∈ sortedHighCountLetters letters ↔
      2 ≤ letters.count letter := by
  rw [sortedDoubledLetters_mem_iff,
    sortedHighCountLetters_mem_iff]
  omega

theorem sortedMultiplicityClasses_disjoint (letters : List Nat) :
    forall letter, letter ∈ sortedDoubledLetters letters ->
      letter ∉ sortedHighCountLetters letters := by
  intro letter doubled high
  rw [sortedDoubledLetters_mem_iff] at doubled
  rw [sortedHighCountLetters_mem_iff] at high
  omega

/-! ## Fixed powers and the Section 12 renderer -/

/-- Render the same fixed exponent for every label. -/
def renderCopies (exponent : Nat) (labels : List Nat) : List Nat :=
  labels.flatMap fun letter => List.replicate exponent letter

def renderSquares (labels : List Nat) : List Nat :=
  renderCopies 2 labels

def renderCubes (labels : List Nat) : List Nat :=
  renderCopies 3 labels

theorem renderCopies_append
    (exponent : Nat) (left right : List Nat) :
    renderCopies exponent (left ++ right) =
      renderCopies exponent left ++ renderCopies exponent right := by
  simp [renderCopies]

theorem renderSquares_eq_s5_107 (labels : List Nat) :
    renderSquares labels = S5_107.renderMultipleSquares labels := by
  induction labels with
  | nil => rfl
  | cons letter rest induction =>
      simp [renderSquares, renderCopies,
        S5_107.renderMultipleSquares, induction]


/-! ## Alpha data and renderer -/

/-- Turn a nonempty endpoint run into one render unit. -/
def optionalRun : List Nat -> List (List Nat)
  | [] => []
  | first :: rest => [first :: rest]

/-- Executable data for the alpha form of Lemma 15.3. `separated` is the
number of doubled labels whose two copies are separated by one or two units;
the remaining doubled labels are rendered as adjacent squares. -/
structure AlphaRenderData where
  stem : List Nat
  doubled : List Nat
  separated : Nat
  units : List (List Nat)
  suffix : List Nat

def alphaRenderData (letters : List Nat) : AlphaRenderData :=
  let doubled := sortedDoubledLetters letters
  let middle :=
    S5_107.sortedSimpleBlocks (S5_107.interiorSimpleBlocks letters)
  let suffix := S5_107.finalSimpleBlock letters
  if 2 * doubled.length - 1 ≤ middle.length then
    { stem := S5_107.initialSimpleBlock letters
      doubled := doubled
      separated := doubled.length
      units := middle ++ optionalRun suffix
      suffix := [] }
  else
    { stem := S5_107.initialSimpleBlock letters
      doubled := doubled
      separated := (middle.length + 1) / 2
      units := middle
      suffix := suffix }

/-- Consume up to two simple-run units around each separated doubled label.
The total fallback cases make the renderer usable before the alpha population
invariants have been proved. -/
def renderAlphaPairs : Nat -> List Nat -> List (List Nat) -> List Nat
  | 0, doubled, _ => renderSquares doubled
  | _ + 1, [], _ => []
  | remaining + 1, letter :: rest, [] =>
      letter :: letter :: renderAlphaPairs remaining rest []
  | remaining + 1, letter :: rest, [unit] =>
      letter :: (unit ++
        letter :: renderAlphaPairs remaining rest [])
  | remaining + 1, letter :: rest, first :: second :: units =>
      letter :: (first ++ letter :: (second ++
        renderAlphaPairs remaining rest units))

def renderAlphaData (data : AlphaRenderData) : List Nat :=
  data.stem ++
    renderAlphaPairs data.separated data.doubled data.units ++
      data.suffix

def alphaCanonicalList (letters : List Nat) : List Nat :=
  renderAlphaData (alphaRenderData letters)

@[simp]
theorem alphaRenderData_prefix (letters : List Nat) :
    (alphaRenderData letters).stem =
      S5_107.initialSimpleBlock letters := by
  simp only [alphaRenderData]
  split <;> rfl

@[simp]
theorem alphaRenderData_doubled (letters : List Nat) :
    (alphaRenderData letters).doubled =
      sortedDoubledLetters letters := by
  simp only [alphaRenderData]
  split <;> rfl

@[simp]
theorem renderAlphaPairs_zero
    (doubled : List Nat) (units : List (List Nat)) :
    renderAlphaPairs 0 doubled units = renderSquares doubled :=
  rfl

theorem alphaCanonicalList_eq_render (letters : List Nat) :
    alphaCanonicalList letters =
      renderAlphaData (alphaRenderData letters) :=
  rfl

/-- Idempotence reduces to the structural fact that re-reading rendered alpha
data recovers the same data. This separates the combinatorial parser theorem
from all semigroup derivation arguments. -/
theorem alphaCanonicalList_idempotent_of_data_stable
    (letters : List Nat)
    (stable :
      alphaRenderData (alphaCanonicalList letters) =
        alphaRenderData letters) :
    alphaCanonicalList (alphaCanonicalList letters) =
      alphaCanonicalList letters := by
  simpa only [alphaCanonicalList] using
    congrArg renderAlphaData stable

/-! ## Beta data and renderer -/

/-- Executable data for the beta form of Lemma 15.4. When `terminalHigh` is
true, one final sorted high-count cube block is rendered after all units. -/
structure BetaRenderData where
  stem : List Nat
  doubled : List Nat
  high : List Nat
  units : List (List Nat)
  terminalHigh : Bool

def betaRenderData (letters : List Nat) : BetaRenderData :=
  let middle :=
    S5_107.sortedSimpleBlocks (S5_107.interiorSimpleBlocks letters)
  match S5_107.finalSimpleBlock letters with
  | [] =>
      { stem := S5_107.initialSimpleBlock letters
        doubled := sortedDoubledLetters letters
        high := sortedHighCountLetters letters
        units := middle
        terminalHigh := true }
  | first :: rest =>
      { stem := S5_107.initialSimpleBlock letters
        doubled := sortedDoubledLetters letters
        high := sortedHighCountLetters letters
        units := middle ++ [first :: rest]
        terminalHigh := false }

/-- Put one high-count cube block before every simple-run unit. -/
def renderBetaUnits (highBlock : List Nat) :
    List (List Nat) -> List Nat
  | [] => []
  | unit :: units =>
      highBlock ++ unit ++ renderBetaUnits highBlock units

def renderBetaData (data : BetaRenderData) : List Nat :=
  let highBlock := renderCubes data.high
  data.stem ++ renderSquares data.doubled ++
    renderBetaUnits highBlock data.units ++
      if data.terminalHigh then highBlock else []

def betaCanonicalList (letters : List Nat) : List Nat :=
  renderBetaData (betaRenderData letters)

@[simp]
theorem betaRenderData_prefix (letters : List Nat) :
    (betaRenderData letters).stem =
      S5_107.initialSimpleBlock letters := by
  cases finalShape : S5_107.finalSimpleBlock letters with
  | nil => simp [betaRenderData, finalShape]
  | cons first rest => simp [betaRenderData, finalShape]

@[simp]
theorem betaRenderData_doubled (letters : List Nat) :
    (betaRenderData letters).doubled =
      sortedDoubledLetters letters := by
  cases finalShape : S5_107.finalSimpleBlock letters with
  | nil => simp [betaRenderData, finalShape]
  | cons first rest => simp [betaRenderData, finalShape]

@[simp]
theorem betaRenderData_high (letters : List Nat) :
    (betaRenderData letters).high =
      sortedHighCountLetters letters := by
  cases finalShape : S5_107.finalSimpleBlock letters with
  | nil => simp [betaRenderData, finalShape]
  | cons first rest => simp [betaRenderData, finalShape]

theorem renderBetaUnits_append
    (highBlock : List Nat) (left right : List (List Nat)) :
    renderBetaUnits highBlock (left ++ right) =
      renderBetaUnits highBlock left ++
        renderBetaUnits highBlock right := by
  induction left with
  | nil => rfl
  | cons unit units induction =>
      simp [renderBetaUnits, induction, List.append_assoc]

theorem betaCanonicalList_eq_render (letters : List Nat) :
    betaCanonicalList letters =
      renderBetaData (betaRenderData letters) :=
  rfl

/-- Beta idempotence has the same parser-stability boundary as alpha
idempotence and remains independent of the Section 15 identity basis. -/
theorem betaCanonicalList_idempotent_of_data_stable
    (letters : List Nat)
    (stable :
      betaRenderData (betaCanonicalList letters) =
        betaRenderData letters) :
    betaCanonicalList (betaCanonicalList letters) =
      betaCanonicalList letters := by
  simpa only [betaCanonicalList] using
    congrArg renderBetaData stable

/-! ## Total branch dispatcher -/

inductive CanonicalBranch
  | simple
  | alpha
  | beta
deriving DecidableEq

def canonicalBranch (letters : List Nat) : CanonicalBranch :=
  match sortedHighCountLetters letters with
  | _ :: _ => .beta
  | [] =>
      match sortedDoubledLetters letters with
      | _ :: _ => .alpha
      | [] => .simple

def canonicalList (letters : List Nat) : List Nat :=
  match canonicalBranch letters with
  | .simple => letters
  | .alpha => alphaCanonicalList letters
  | .beta => betaCanonicalList letters

theorem canonicalBranch_eq_simple
    (letters : List Nat)
    (high : sortedHighCountLetters letters = [])
    (doubled : sortedDoubledLetters letters = []) :
    canonicalBranch letters = .simple := by
  simp [canonicalBranch, high, doubled]

theorem canonicalBranch_eq_alpha
    (letters : List Nat)
    (high : sortedHighCountLetters letters = [])
    (doubled : sortedDoubledLetters letters = first :: rest) :
    canonicalBranch letters = .alpha := by
  simp [canonicalBranch, high, doubled]

theorem canonicalBranch_eq_beta
    (letters : List Nat)
    (high : sortedHighCountLetters letters = first :: rest) :
    canonicalBranch letters = .beta := by
  simp [canonicalBranch, high]

theorem canonicalList_eq_self_of_no_multiple
    (letters : List Nat)
    (multiple : S5_107.sortedMultipleLetters letters = []) :
    canonicalList letters = letters := by
  have high : sortedHighCountLetters letters = [] := by
    simp [sortedHighCountLetters, multiple]
  have doubled : sortedDoubledLetters letters = [] := by
    simp [sortedDoubledLetters, multiple]
  simp [canonicalList, canonicalBranch, high, doubled]

/-- The all-simple branch is unconditionally idempotent. -/
theorem canonicalList_idempotent_of_no_multiple
    (letters : List Nat)
    (multiple : S5_107.sortedMultipleLetters letters = []) :
    canonicalList (canonicalList letters) = canonicalList letters := by
  have fixed := canonicalList_eq_self_of_no_multiple letters multiple
  simpa only [fixed]

end CanonicalData

end SemigroupBasis.CoRoots.Order6SporadicSection15

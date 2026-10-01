import SemigroupBasis.CoRoots.Order6SporadicSection15BranchFacts
import SemigroupBasis.CoRoots.Order6SporadicSection15ParsedWords

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace BetaScaffoldData

/-- Doubled labels in the deterministic Section 15 order. -/
def doubledLabels (letters : List Nat) : List Nat :=
  CanonicalData.sortedDoubledLetters letters

/-- High-count labels in the deterministic Section 15 order. -/
def highLabels (letters : List Nat) : List Nat :=
  CanonicalData.sortedHighCountLetters letters

/-- The repeated nonempty beta anchor when the dispatcher selects `.beta`. -/
def highBlock (letters : List Nat) : List Nat :=
  CanonicalData.renderCubes (highLabels letters)

def interiorUnits (letters : List Nat) : List (List Nat) :=
  S5_107.interiorSimpleBlocks letters

def sortedInteriorUnits (letters : List Nat) : List (List Nat) :=
  S5_107.sortedSimpleBlocks (interiorUnits letters)

/-- Preserve the source order of interior simple units. A nonempty final simple
block remains the final unit; when it is absent, the renderer emits a terminal
high block instead. -/
def rawUnits (letters : List Nat) : List (List Nat) :=
  match S5_107.finalSimpleBlock letters with
  | [] => interiorUnits letters
  | first :: rest =>
      interiorUnits letters ++ [first :: rest]

def terminalHigh (letters : List Nat) : Bool :=
  match S5_107.finalSimpleBlock letters with
  | [] => true
  | _ :: _ => false

/-- The beta scaffold before sorting its interior simple units. Doubled and
high-count labels already use their deterministic orders. -/
def scaffoldData (letters : List Nat) : CanonicalData.BetaRenderData :=
  { stem := S5_107.initialSimpleBlock letters
    doubled := doubledLabels letters
    high := highLabels letters
    units := rawUnits letters
    terminalHigh := terminalHigh letters }

def scaffoldList (letters : List Nat) : List Nat :=
  CanonicalData.renderBetaData (scaffoldData letters)

/-- Replace only the raw interior-unit order with the canonical sorted order. -/
def sortedScaffoldData (letters : List Nat) :
    CanonicalData.BetaRenderData :=
  { scaffoldData letters with
    units := (CanonicalData.betaRenderData letters).units }

def sortedScaffoldList (letters : List Nat) : List Nat :=
  CanonicalData.renderBetaData (sortedScaffoldData letters)

theorem highLabels_ne_nil_of_branch_beta
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    highLabels letters ≠ [] :=
  CanonicalData.sortedHighCountLetters_ne_nil_of_branch_beta branch

theorem highBlock_ne_nil_of_branch_beta
    {letters : List Nat}
    (branch : CanonicalData.canonicalBranch letters = .beta) :
    highBlock letters ≠ [] := by
  obtain ⟨first, rest, shape⟩ :=
    List.exists_cons_of_ne_nil (highLabels_ne_nil_of_branch_beta branch)
  simp [highBlock, CanonicalData.renderCubes,
    CanonicalData.renderCopies, shape]

theorem interiorUnits_perm_sortedInteriorUnits (letters : List Nat) :
    (interiorUnits letters).Perm (sortedInteriorUnits letters) := by
  unfold sortedInteriorUnits S5_107.sortedSimpleBlocks
  exact (List.mergeSort_perm _ _).symm

theorem interiorUnits_nonempty
    (letters : List Nat) (unit : List Nat)
    (member : unit ∈ interiorUnits letters) :
    unit ≠ [] := by
  exact S5_107.simpleBlocks_blocks_nonempty letters unit
    ((S5_107.mem_interiorSimpleBlocks_iff letters unit).mp member).1

@[simp]
theorem scaffoldData_prefix (letters : List Nat) :
    (scaffoldData letters).stem =
      S5_107.initialSimpleBlock letters :=
  rfl

@[simp]
theorem scaffoldData_doubled (letters : List Nat) :
    (scaffoldData letters).doubled =
      CanonicalData.sortedDoubledLetters letters :=
  rfl

@[simp]
theorem scaffoldData_high (letters : List Nat) :
    (scaffoldData letters).high =
      CanonicalData.sortedHighCountLetters letters :=
  rfl

@[simp]
theorem scaffoldData_units (letters : List Nat) :
    (scaffoldData letters).units = rawUnits letters :=
  rfl

@[simp]
theorem scaffoldData_terminalHigh (letters : List Nat) :
    (scaffoldData letters).terminalHigh = terminalHigh letters :=
  rfl

/-- Sorting only the interior simple units turns the scaffold data into the
exact executable beta canonical data. -/
theorem sortedScaffoldData_eq_betaRenderData (letters : List Nat) :
    sortedScaffoldData letters =
      CanonicalData.betaRenderData letters := by
  cases finalShape : S5_107.finalSimpleBlock letters with
  | nil =>
      simp [sortedScaffoldData, scaffoldData, doubledLabels, highLabels,
        rawUnits, terminalHigh, CanonicalData.betaRenderData, finalShape]
  | cons first rest =>
      simp [sortedScaffoldData, scaffoldData, doubledLabels, highLabels,
        rawUnits, terminalHigh, CanonicalData.betaRenderData, finalShape]

theorem sortedScaffoldList_eq_betaCanonicalList (letters : List Nat) :
    sortedScaffoldList letters =
      CanonicalData.betaCanonicalList letters := by
  rw [sortedScaffoldList, sortedScaffoldData_eq_betaRenderData]
  rfl

end BetaScaffoldData

end SemigroupBasis.CoRoots.Order6SporadicSection15

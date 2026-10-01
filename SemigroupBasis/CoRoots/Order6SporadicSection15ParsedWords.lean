import SemigroupBasis.CoRoots.S5_107ScannerEndpoints

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace ParsedWords

/-! ## Reused terminated-word parser

Section 15 uses the established `S5_107` scanner unchanged.  This namespace
only gives its output local names and records the structural facts needed by
the alpha and beta normalizers.
-/

abbrev Factor := List Nat × Nat

/-- Simple blocks paired with their following globally non-simple marker. -/
def factors (letters : List Nat) : List Factor :=
  S5_107.terminatedBlocks letters

/-- The globally simple suffix following the final parsed marker. -/
def finalBlock (letters : List Nat) : List Nat :=
  S5_107.terminatedFinalBlock letters

/-- Render parsed factors without changing their marker multiplicities. -/
def renderFactors (parsed : List Factor) : List Nat :=
  S5_107.renderTerminatedBlocks parsed

/-- The reused parser reconstructs the source list literally. -/
theorem reconstruct (letters : List Nat) :
    renderFactors (factors letters) ++ finalBlock letters = letters := by
  simpa [renderFactors, factors, finalBlock] using
    S5_107.terminatedBlocks_render letters

/-- The scanner suffix is the maximal final globally simple block. -/
theorem finalBlock_eq_finalSimpleBlock (letters : List Nat) :
    finalBlock letters = S5_107.finalSimpleBlock letters := by
  simpa [finalBlock] using
    S5_107.terminatedFinalBlock_eq_finalSimpleBlock letters

/-- The complete simple-block parser is recovered from the same factors and
final suffix. -/
theorem simpleBlocks_eq_parsed (letters : List Nat) :
    S5_107.simpleBlocks letters =
      S5_107.simpleBlocksFromTerminated
        (factors letters) (finalBlock letters) := by
  simpa [factors, finalBlock] using
    S5_107.simpleBlocks_eq_simpleBlocksFromTerminated letters

/-- For a nonempty factor list, the first carried block is the initial simple
block and the nonempty blocks carried by the tail are exactly the interior
simple blocks. -/
theorem factors_cons_endpoint_blocks
    (letters : List Nat)
    (first : Factor)
    (rest : List Factor)
    (shape : factors letters = first :: rest) :
    first.1 = S5_107.initialSimpleBlock letters ∧
      S5_107.nonemptyTerminatedBlocks rest =
        S5_107.interiorSimpleBlocks letters := by
  simpa [factors] using
    S5_107.terminatedBlocks_cons_endpoint_blocks
      letters first rest shape

theorem firstBlock_eq_initialSimpleBlock
    (letters : List Nat)
    (first : Factor)
    (rest : List Factor)
    (shape : factors letters = first :: rest) :
    first.1 = S5_107.initialSimpleBlock letters :=
  (factors_cons_endpoint_blocks letters first rest shape).1

theorem nonemptyRestBlocks_eq_interiorSimpleBlocks
    (letters : List Nat)
    (first : Factor)
    (rest : List Factor)
    (shape : factors letters = first :: rest) :
    S5_107.nonemptyTerminatedBlocks rest =
      S5_107.interiorSimpleBlocks letters :=
  (factors_cons_endpoint_blocks letters first rest shape).2

/-- Package all endpoint facts for callers that have exposed the first
factor. -/
theorem endpoint_blocks_of_cons
    (letters : List Nat)
    (first : Factor)
    (rest : List Factor)
    (shape : factors letters = first :: rest) :
    first.1 = S5_107.initialSimpleBlock letters ∧
      S5_107.nonemptyTerminatedBlocks rest =
        S5_107.interiorSimpleBlocks letters ∧
      finalBlock letters = S5_107.finalSimpleBlock letters := by
  exact
    ⟨firstBlock_eq_initialSimpleBlock letters first rest shape,
      nonemptyRestBlocks_eq_interiorSimpleBlocks
        letters first rest shape,
      finalBlock_eq_finalSimpleBlock letters⟩

/-- Every letter carried in a parsed simple block is globally simple. -/
theorem factor_block_letter_simple
    (letters : List Nat)
    (factor : Factor)
    (factorMember : factor ∈ factors letters)
    (letter : Nat)
    (letterMember : letter ∈ factor.1) :
    letters.count letter = 1 := by
  exact
    S5_107.terminatedBlocks_block_simple
      letters factor factorMember letter letterMember

/-- Every parsed marker is globally multiple in the source list. -/
theorem factor_marker_multiple
    (letters : List Nat)
    (factor : Factor)
    (factorMember : factor ∈ factors letters) :
    2 ≤ letters.count factor.2 := by
  exact
    S5_107.terminatedBlocks_marker_multiple
      letters factor factorMember

/-- Every letter in the final parser suffix is globally simple. -/
theorem finalBlock_letter_simple
    (letters : List Nat)
    (letter : Nat)
    (letterMember : letter ∈ finalBlock letters) :
    letters.count letter = 1 := by
  exact
    S5_107.terminatedFinalBlock_letter_simple
      letters letter letterMember

end ParsedWords

end SemigroupBasis.CoRoots.Order6SporadicSection15

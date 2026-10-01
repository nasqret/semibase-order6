import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSemanticSimpleAdjacency
import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedCanonicalGapProjection

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant

open RootFamily CanonicalPresentation FactorCodec SimpleFactorInvariant

/-- Explicit representation boundary: the two established adjacency APIs
have different argument orders but assert the same literal occurrence. -/
theorem adjacency_argument_bridge (letters : List Nat) (first second : Nat) :
    SimpleFactorGraph.Adjacent letters first second ↔
      SemanticSimpleAdjacency.Adjacent first second letters := Iff.rfl

theorem semantic_same_simple (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target) :
    SimpleFactorGraph.SameSimple source.toList target.toList := by
  intro letter
  exact (SemanticSimpleAdjacency.semantic_occurrence_categories
    source target equalEval letter).2.1

theorem semantic_same_edges (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target) :
    SimpleFactorGraph.SameEdges source.toList target.toList := by
  intro first second different firstOnce secondOnce
  have semanticEdge :
      SemanticSimpleAdjacency.Adjacent first second source.toList ↔
        SemanticSimpleAdjacency.Adjacent first second target.toList :=
    SemanticSimpleAdjacency.semantic_simple_adjacency
      source target equalEval first second different firstOnce secondOnce
  exact (adjacency_argument_bridge source.toList first second).trans
    (semanticEdge.trans (adjacency_argument_bridge target.toList first second).symm)

/-- Actual semantic equality supplies both hypotheses of the arbitrary-list
factor graph theorem; no finite alphabet or word-length bound occurs here. -/
theorem semantic_maximal_simple (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target) (piece : List Nat) :
    SimpleFactorGraph.MaximalSimple source.toList piece ↔
      SimpleFactorGraph.MaximalSimple target.toList piece :=
  SimpleFactorGraph.maximal_simple_iff source.toList target.toList piece
    (semantic_same_simple source target equalEval)
    (semantic_same_edges source target equalEval)

theorem semantic_simple_factor (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target) (piece : Word Nat) :
    piece ∈ simpleFactors source ↔ piece ∈ simpleFactors target :=
  SimpleFactorRepresentation.simpleFactors_set_transfer source target
    (semantic_same_simple source target equalEval)
    (semantic_same_edges source target equalEval) piece

/-- Membership in the actual canonical nonempty gap set is a semantic
invariant. Empty gaps and comparison of the gap order remain separate. -/
theorem semantic_nonempty_gap (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target) (gap : List Nat) (nonempty : gap ≠ []) :
    (∃ entry ∈ left.chunks, MaximalFactors.flatten entry.1 = gap) ↔
      ∃ entry ∈ right.chunks, MaximalFactors.flatten entry.1 = gap :=
  CanonicalGapProjection.nonempty_gap_set_transfer source target left right
    (semantic_same_simple source target equalEval)
    (semantic_same_edges source target equalEval) gap nonempty

/-- This discharges target-marker simplicity for the existing root-range
interface from source-marker simplicity and equality of word functions. -/
theorem semantic_simple_marker (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (marker : Nat) (sourceSimple : source.toList.count marker = 1) :
    target.toList.count marker = 1 :=
  (semantic_same_simple source target equalEval marker).mp sourceSimple

/-- The nonsimple support union and every nonempty canonical gap now follow
from actual C8 semantic equality; individual root partitions are not assumed. -/
theorem semantic_form_invariants (source target : Word Nat)
    (equalEval : SemanticSimpleAdjacency.EqualEval source target)
    (left : Form source) (right : Form target) :
    (∀ letter, Covered left.roots letter ↔ Covered right.roots letter) ∧
    (∀ gap : List Nat, gap ≠ [] →
      ((∃ entry ∈ left.chunks, MaximalFactors.flatten entry.1 = gap) ↔
        ∃ entry ∈ right.chunks, MaximalFactors.flatten entry.1 = gap)) := by
  constructor
  · intro letter
    exact SemanticSimpleAdjacency.semantic_covered_iff source target equalEval left right letter
  · intro gap nonempty
    exact semantic_nonempty_gap source target equalEval left right gap nonempty

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant.adjacency_argument_bridge
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant.semantic_same_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant.semantic_same_edges
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant.semantic_maximal_simple
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant.semantic_simple_factor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant.semantic_nonempty_gap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant.semantic_simple_marker
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SemanticGapInvariant.semantic_form_invariants

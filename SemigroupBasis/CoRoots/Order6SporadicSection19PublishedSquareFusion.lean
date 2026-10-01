import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedBinaryPerfect

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareFusion

open CrossFactor CrossSweep BinaryPowers FactorContexts OccurrenceWitnesses
  MarkedZones SquareCoalescing OrderedSquareForm

/-- Fuse duplicated marked words INSIDE a square. This does not assert the
false standalone identity `u²v² = (uv)²`. All four edges use the published
sandwich laws, with the actual nonempty words as substitution images. -/
theorem square_fusion (u v : Word Nat) :
    Derives basis (square (u ++ u) (v ++ v)) (square u v) := by
  let first : Word Nat := u ++ (v ++ (v ++ (u ++ (u ++ (v ++ v)))))
  let second : Word Nat := u ++ (v ++ (v ++ (u ++ (v ++ v))))
  let third : Word Nat := u ++ (v ++ (u ++ (v ++ v)))
  have edge1 : Derives basis (square (u ++ u) (v ++ v)) first := by
    simpa only [first, square, Word.append_assoc] using
      (Derives.appendRight (sandwich_left u (v ++ v)) ((u ++ v) ++ v))
  have edge2 : Derives basis first second := by
    simpa only [first, second, Word.append_assoc] using
      (Derives.appendRight (sandwich_right u (v ++ v)) (v ++ v))
  have edge3 : Derives basis second third := by
    simpa only [second, third, Word.append_assoc] using
      (Derives.prepend u (Derives.appendRight (sandwich_left v u) v))
  have edge4 : Derives basis third (square u v) := by
    simpa only [third, square, Word.append_assoc] using
      (Derives.prepend u (sandwich_right v u))
  exact edge1.trans (edge2.trans (edge3.trans edge4))

/-- Fusion preserves both actual exterior contexts, including empty ones. -/
theorem square_fusion_frame (u v : Word Nat) (before after : List Nat) :
    Derives basis
      (Context.frame (contextWord before) (contextWord after)
        (square (u ++ u) (v ++ v)))
      (Context.frame (contextWord before) (contextWord after) (square u v)) :=
  Context.frame_derives (square_fusion u v) (contextWord before) (contextWord after)

/-- Fuse every marked square without changing any of its actual separators. -/
theorem square_fusion_chain (u v : Word Nat) (gaps : List (List Nat)) :
    Derives basis (chain (square (u ++ u) (v ++ v)) gaps)
      (chain (square u v) gaps) :=
  chain_derives (square_fusion u v) gaps

/-- The generalized-block algebra step through the full recorded frame.
No claim about sorting supports, maximal original factors, or global
canonical-form termination is hidden in this statement. -/
theorem square_fusion_framed_chain (u v : Word Nat) (gaps : List (List Nat))
    (before after : List Nat) :
    Derives basis
      (Context.frame (contextWord before) (contextWord after)
        (chain (square (u ++ u) (v ++ v)) gaps))
      (Context.frame (contextWord before) (contextWord after)
        (chain (square u v) gaps)) :=
  framed_chain_derives (square_fusion u v) gaps before after

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareFusion

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareFusion.square_fusion
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareFusion.square_fusion_frame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareFusion.square_fusion_chain
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareFusion.square_fusion_framed_chain

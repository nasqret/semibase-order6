import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedPowers

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra

open CrossFactor CrossSweep CrossLeftSweep AnchorPropagation MiddleSweep BinaryPowers

theorem square_idempotent (u v : Word Nat) :
    Derives basis (square u v ++ square u v) (square u v) := by
  have step := (Derives.appendRight (cube (u ++ v)) (u ++ v)).trans (cube (u ++ v))
  simpa only [square, Word.append_assoc] using step

theorem square_copies (u v : Word Nat) (n : Nat) :
    Derives basis (copies (square u v) n) (square u v) := by
  induction n with
  | zero => exact Derives.refl _
  | succ n ih =>
      change Derives basis (copies (square u v) n ++ square u v) (square u v)
      exact (Derives.appendRight ih (square u v)).trans (square_idempotent u v)

/-- Two occurrences of the marked block suffice to perfect the first,
while retaining the entire separator and the second block verbatim. -/
theorem left_pair_square (u v : Word Nat) (kGap : Option (Word Nat)) :
    Derives basis (gap (bud u v) kGap ++ bud u v)
      (gap (square u v) kGap ++ bud u v) := by
  have expand : Derives basis
      (gap (bud u v) kGap ++ bud u v)
      (gap ((v ++ v) ++ (u ++ u)) kGap ++ bud u v) := by
    have step := Derives.prepend (v ++ v)
      (duplicate_first u (some (frontGap kGap (v ++ v))))
    cases kGap <;>
      simpa only [bud, gap, frontGap, Word.append_assoc] using step
  have rotate : Derives basis
      (gap ((v ++ v) ++ (u ++ u)) kGap ++ bud u v)
      (gap (square v u) kGap ++ bud u v) := by
    have step := Derives.prepend v
      (CrossFactor.e_front v u none (some (gap u kGap ++ v)))
    cases kGap <;>
      simpa only [bud, square, gap, Word.append_assoc] using step
  have order := Derives.appendRight (gap_derives (square_comm v u) kGap) (bud u v)
  exact expand.trans (rotate.trans order)

/-- Perfect a right marked block using the actual C1 anchor.
The e-swap keeps its earlier u/v witnesses; no standalone u²v² law is used. -/
theorem right_bud_square (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis
      (gap (anchor u v hGap) kGap ++ bud u v)
      (gap (anchor u v hGap) kGap ++ square u v) := by
  have expand : Derives basis
      (gap (anchor u v hGap) kGap ++ bud u v)
      (gap (anchor u v hGap) kGap ++ ((v ++ v) ++ (u ++ u))) := by
    have step := Derives.prepend ((gap u hGap ++ v) ++ v)
      (duplicate_last u (some (frontGap kGap (v ++ v))))
    cases kGap <;>
      simpa only [anchor, bud, gap, frontGap, Word.append_assoc] using step
  have rotate : Derives basis
      (gap (anchor u v hGap) kGap ++ ((v ++ v) ++ (u ++ u)))
      (gap (anchor u v hGap) kGap ++ square v u) := by
    have step := Derives.appendRight
      (CrossFactor.e_back u v hGap (some (gap (v ++ u) kGap ++ v))).symm u
    cases kGap <;>
      simpa only [anchor, square, gap, Word.append_assoc] using step
  have order := Derives.prepend (gap (anchor u v hGap) kGap) (square_comm v u)
  exact expand.trans (rotate.trans order)

theorem left_bud_square (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis
      (gap (bud u v) kGap ++ anchor u v hGap)
      (gap (square u v) kGap ++ anchor u v hGap) := by
  have step := left_pair_square u v (some (gap (frontGap kGap u) hGap))
  cases hGap <;> cases kGap <;>
    simpa only [anchor, bud, square, gap, frontGap, Word.append_assoc] using step

/-- The distinguished seed itself becomes two perfect binary squares,
with its original middle word unchanged. Empty middle permits coalescing. -/
theorem anchor_perfect (u v : Word Nat) (hGap : Option (Word Nat)) :
    Derives basis (anchor u v hGap) (gap (square u v) hGap ++ square u v) := by
  have seed : Derives basis (anchor u v hGap) (gap (bud u v) hGap ++ bud u v) := by
    have step := seed_left u v hGap
    cases hGap <;>
      simpa only [anchor, bud, gap, Word.append_assoc] using step
  have first := left_pair_square u v hGap
  have restore := Derives.appendRight
    (gap_derives (anchor_empty u v).symm hGap) (bud u v)
  have second := right_bud_square u v none hGap
  have finish := Derives.appendRight
    (gap_derives (anchor_empty u v) hGap) (square u v)
  exact seed.trans (first.trans (restore.trans (second.trans finish)))

theorem middle_square_one (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis
      (anchor u v (joinGap (pushGap hGap u) kGap))
      (anchor u v (joinGap (pushGap hGap (square u v)) kGap)) := by
  have seed : Derives basis (anchor u v kGap) (gap (bud u v) kGap ++ bud u v) := by
    have step := seed_left u v kGap
    cases kGap <;>
      simpa only [anchor, bud, gap, Word.append_assoc] using step
  have localStep := seed.trans (left_pair_square u v kGap)
  have step := Derives.prepend (gap u hGap) localStep
  simpa only [anchor, bud, gap_join, gap_push, gap_append, Word.append_assoc] using step

/-- The remaining order of the repeated-v witness: it lies inside the
short anchor's middle, rather than before or after that anchor. -/
theorem c1_seed_middle (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis
      (shortAnchor u v (joinGap (pushGap hGap v) kGap))
      (anchor u v (joinGap (pushGap hGap v) kGap)) := by
  have step := Derives.prepend (gap u hGap)
    (Derives.appendRight (duplicate_last v kGap) u)
  simpa only [shortAnchor, anchor, gap_join, gap_push, gap_append, Word.append_assoc] using step

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra.square_idempotent
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra.square_copies
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra.left_pair_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra.right_bud_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra.left_bud_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra.anchor_perfect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra.middle_square_one
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.SquareAlgebra.c1_seed_middle

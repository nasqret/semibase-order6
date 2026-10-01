import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedMiddleSweep

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers

open CrossFactor CrossSweep CrossLeftSweep AnchorPropagation MiddleSweep

theorem cube (u : Word Nat) :
    Derives basis ((u ++ u) ++ u) (u ++ u) := by
  have step : Derives basis
      (a_cube.lhs.bind (fun _ : Nat => u))
      (a_cube.rhs.bind (fun _ : Nat => u)) :=
    derives_a_cube.subst (fun _ : Nat => u)
  exact step

theorem sandwich_left (u v : Word Nat) :
    Derives basis (((u ++ u) ++ v) ++ u) ((u ++ v) ++ u) := by
  have step : Derives basis
      (a_left.lhs.bind (fun n : Nat => if n = 0 then u else v))
      (a_left.rhs.bind (fun n : Nat => if n = 0 then u else v)) :=
    derives_a_left.subst (fun n : Nat => if n = 0 then u else v)
  exact step

theorem sandwich_right (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ u) ((u ++ v) ++ u) := by
  have step : Derives basis
      (a_right.lhs.bind (fun n : Nat => if n = 0 then u else v))
      (a_right.rhs.bind (fun n : Nat => if n = 0 then u else v)) :=
    derives_a_right.subst (fun n : Nat => if n = 0 then u else v)
  exact step

/-- An existing second occurrence permits duplication of the first.
The empty gap uses the cube law, never an empty substitution image. -/
theorem duplicate_first (u : Word Nat) (middle : Option (Word Nat)) :
    Derives basis (gap u middle ++ u) (gap (u ++ u) middle ++ u) := by
  cases middle with
  | none => exact (cube u).symm
  | some v => exact (sandwich_left u v).symm

theorem duplicate_last (u : Word Nat) (middle : Option (Word Nat)) :
    Derives basis (gap u middle ++ u) ((gap u middle ++ u) ++ u) := by
  cases middle with
  | none => exact (cube u).symm
  | some v => exact (sandwich_right u v).symm

/-- A positive number of copies. No empty word is introduced. -/
def copies (u : Word Nat) : Nat → Word Nat
  | 0 => u
  | n + 1 => copies u n ++ u

theorem copies_stabilize (u : Word Nat) (n : Nat) :
    Derives basis (copies u (n + 1)) (u ++ u) := by
  induction n with
  | zero => exact Derives.refl _
  | succ n ih =>
      change Derives basis (copies u (n + 1) ++ u) (u ++ u)
      exact (Derives.appendRight ih u).trans (cube u)

def shortAnchor (u v : Word Nat) (middle : Option (Word Nat)) : Word Nat :=
  (gap u middle ++ v) ++ u

/-- A prior occurrence of v supplies the repeated-letter witness needed
to turn the actual C1 adjacency u H v u into the existing u H v v u seed. -/
theorem c1_seed_left (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis
      (gap v kGap ++ shortAnchor u v hGap)
      (gap v kGap ++ anchor u v hGap) := by
  have step := Derives.appendRight
    (duplicate_last v (some (gap (frontGap kGap u) hGap))) u
  cases hGap <;> cases kGap <;>
    simpa only [shortAnchor, anchor, gap, frontGap, Word.append_assoc] using step

/-- The other witness order: a later occurrence of v supplies the seed. -/
theorem c1_seed_right (u v : Word Nat) (hGap kGap : Option (Word Nat)) :
    Derives basis
      (gap (shortAnchor u v hGap) kGap ++ v)
      (gap (anchor u v hGap) kGap ++ v) := by
  have step := Derives.prepend (gap u hGap)
    (duplicate_first v (some (gap u kGap)))
  cases hGap <;> cases kGap <;>
    simpa only [shortAnchor, anchor, gap, Word.append_assoc] using step

def square (u v : Word Nat) : Word Nat := (u ++ v) ++ (u ++ v)

/-- Binary perfect squares can be put in the chosen alphabetic order.
This does not assert the false standalone law u^2 v^2 = (uv)^2. -/
theorem square_comm (u v : Word Nat) :
    Derives basis (square u v) (square v u) := by
  have first : Derives basis (square u v) (((u ++ v) ++ v) ++ u) := by
    simpa only [square, gap, Word.append_assoc] using
      (CrossFactor.e_back u v none none)
  have second : Derives basis (square v u) (((u ++ v) ++ v) ++ u) := by
    simpa only [square, gap, Word.append_assoc] using
      (CrossFactor.e_front v u none none)
  exact first.trans second.symm

theorem anchor_empty (u v : Word Nat) :
    Derives basis (anchor u v none) (square u v) := by
  simpa only [anchor, square, gap, Word.append_assoc] using
    (CrossFactor.e_back u v none none).symm

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.cube
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.sandwich_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.sandwich_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.duplicate_first
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.duplicate_last
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.copies_stabilize
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.c1_seed_left
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.c1_seed_right
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.square_comm
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPowers.anchor_empty

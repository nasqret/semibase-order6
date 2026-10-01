import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_11S5_788Profile

/-!
# Exact displayed-law macros for `S3_11 x S5_788`

This module names the arbitrary-block substitutions of the frozen eighteen
displayed laws.  Every macro derives directly in the exact C2 basis; none
imports the ordinary `S5_788` basis or the stronger Ford/Lord profile.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

open SemigroupBasis

abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_11S5_788

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- Substitute arbitrary nonempty words into one exact displayed law. -/
theorem derivesDisplayedSubstitution
    (identity : Identity Nat) (member : identity ∈ targetBasis)
    (substitution : Nat → Word Nat) :
    Derives targetBasis
      (identity.lhs.bind substitution)
      (identity.rhs.bind substitution) :=
  Derives.subst (Derives.fromBasis member) substitution

/-- `u² = u⁴`. -/
theorem derivesPowerPeriod (u : Word Nat) :
    Derives targetBasis
      (u ++ u) (((u ++ u) ++ u) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0]) (w 0 [0, 0, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0]) (w 0 [0, 0, 0])) (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u u u)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u³ v u = u v u`. -/
theorem derivesTripleLeftContraction (u v : Word Nat) :
    Derives targetBasis
      ((((u ++ u) ++ u) ++ v) ++ u)
      ((u ++ v) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0, 0, 1, 0]) (w 0 [1, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 0, 1, 0]) (w 0 [1, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v u = u v u²`. -/
theorem derivesEndpointTransfer (u v : Word Nat) :
    Derives targetBasis
      (((u ++ u) ++ v) ++ u)
      (((u ++ v) ++ u) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 0]) (w 0 [1, 0, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 0]) (w 0 [1, 0, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v u² = u v u`. -/
theorem derivesSplitEndpointContraction (u v : Word Nat) :
    Derives targetBasis
      ((((u ++ u) ++ v) ++ u) ++ u)
      ((u ++ v) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 0, 0]) (w 0 [1, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 0, 0]) (w 0 [1, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v² = u v u v`. -/
theorem derivesSquareInterleave (u v : Word Nat) :
    Derives targetBasis
      (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ u) ++ v) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 1]) (w 0 [1, 0, 1]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v² = u v² u`. -/
theorem derivesSquareFinalSwitch (u v : Word Nat) :
    Derives targetBasis
      (((u ++ u) ++ v) ++ v)
      (((u ++ v) ++ v) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 1]) (w 0 [1, 1, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v³ = u v u`. -/
theorem derivesMixedContraction (u v : Word Nat) :
    Derives targetBasis
      (((((u ++ u) ++ v) ++ v) ++ v))
      ((u ++ v) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 1, 1]) (w 0 [1, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 1, 1]) (w 0 [1, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v z u = u v u z u`. -/
theorem derivesDoubledInitialClosedMove (u v z : Word Nat) :
    Derives targetBasis
      ((((u ++ u) ++ v) ++ z) ++ u)
      ((((u ++ v) ++ u) ++ z) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 2, 0]) (w 0 [1, 0, 2, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 2, 0]) (w 0 [1, 0, 2, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v z v = u v u z v`. -/
theorem derivesAttachmentInitial (u v z : Word Nat) :
    Derives targetBasis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ u) ++ z) ++ v) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v z v = u v² z u`. -/
theorem derivesAttachmentFinal (u v z : Word Nat) :
    Derives targetBasis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ v) ++ z) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 1, 2, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v z v = u v z u v`. -/
theorem derivesAttachmentCrossing (u v z : Word Nat) :
    Derives targetBasis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ z) ++ u) ++ v) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0, 1]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 0, 1]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u² v z v = u v z v u`. -/
theorem derivesAttachmentTurn (u v z : Word Nat) :
    Derives targetBasis
      ((((u ++ u) ++ v) ++ z) ++ v)
      ((((u ++ v) ++ z) ++ v) ++ u) := by
  have base :
      Derives targetBasis (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 1, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 2, 1, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u v u = u v u³`. -/
theorem derivesRightTripleExpansion (u v : Word Nat) :
    Derives targetBasis
      ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ u) ++ u) := by
  have base :
      Derives targetBasis (w 0 [1, 0]) (w 0 [1, 0, 0, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 0, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u v u = u v u v²`. -/
theorem derivesTrailingSquareExpansion (u v : Word Nat) :
    Derives targetBasis
      ((u ++ v) ++ u)
      ((((u ++ v) ++ u) ++ v) ++ v) := by
  have base :
      Derives targetBasis (w 0 [1, 0]) (w 0 [1, 0, 1, 1]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [1, 0]) (w 0 [1, 0, 1, 1]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u v u = u v² u v`. -/
theorem derivesMiddleSquareExpansion (u v : Word Nat) :
    Derives targetBasis
      ((u ++ v) ++ u)
      ((((u ++ v) ++ v) ++ u) ++ v) := by
  have base :
      Derives targetBasis (w 0 [1, 0]) (w 0 [1, 1, 0, 1]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 0, 1]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u v u = u v³ u`. -/
theorem derivesMiddleTripleExpansion (u v : Word Nat) :
    Derives targetBasis
      ((u ++ v) ++ u)
      ((((u ++ v) ++ v) ++ v) ++ u) := by
  have base :
      Derives targetBasis (w 0 [1, 0]) (w 0 [1, 1, 1, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [1, 0]) (w 0 [1, 1, 1, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v v)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u v u z² = u v z u z`. -/
theorem derivesFinalSquareCrossing (u v z : Word Nat) :
    Derives targetBasis
      ((((u ++ v) ++ u) ++ z) ++ z)
      ((((u ++ v) ++ z) ++ u) ++ z) := by
  have base :
      Derives targetBasis (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

/-- `u v u z² = u v z² u`. -/
theorem derivesFinalSquareTurn (u v z : Word Nat) :
    Derives targetBasis
      ((((u ++ v) ++ u) ++ z) ++ z)
      ((((u ++ v) ++ z) ++ z) ++ u) := by
  have base :
      Derives targetBasis (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]) :=
    Derives.fromBasis
      (e := Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0]))
      (by decide)
  have substituted :=
    Derives.subst base (instantiateThreeWords u v z)
  simpa [w, instantiateThreeWords, Word.bind, Word.singleton,
    Word.append, Word.append_assoc] using substituted

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

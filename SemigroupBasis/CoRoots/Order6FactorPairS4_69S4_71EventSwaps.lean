import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71CountReduction

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateThreeWords
    (x y z : Word Nat) : Nat -> Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisLaw03 :
    Derives basis
      (w 0 [0, 1, 1])
      (w 0 [1, 0, 1]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 0, 1])) (by decide)

private theorem basisLaw04 :
    Derives basis
      (w 0 [0, 1, 1])
      (w 0 [1, 1, 0]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [0, 1, 1]) (w 0 [1, 1, 0])) (by decide)

private theorem basisLaw05 :
    Derives basis
      (w 0 [0, 1, 1])
      (w 1 [0, 0, 1]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [0, 1, 1]) (w 1 [0, 0, 1])) (by decide)

private theorem basisLaw06 :
    Derives basis
      (w 0 [0, 1, 2, 1])
      (w 0 [1, 0, 2, 1]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [0, 1, 2, 1]) (w 0 [1, 0, 2, 1])) (by decide)

private theorem basisLaw07 :
    Derives basis
      (w 0 [0, 1, 2, 1])
      (w 1 [0, 0, 2, 1]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [0, 1, 2, 1]) (w 1 [0, 0, 2, 1])) (by decide)

private theorem basisLaw10 :
    Derives basis
      (w 0 [1, 0, 2, 2])
      (w 0 [1, 2, 0, 2]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 0, 2])) (by decide)

private theorem basisLaw11 :
    Derives basis
      (w 0 [1, 0, 2, 2])
      (w 0 [1, 2, 2, 0]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [1, 2, 2, 0])) (by decide)

private theorem basisLaw12 :
    Derives basis
      (w 0 [1, 0, 2, 2])
      (w 0 [2, 1, 0, 2]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [2, 1, 0, 2])) (by decide)

private theorem basisLaw13 :
    Derives basis
      (w 0 [1, 0, 2, 2])
      (w 0 [2, 1, 2, 0]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [1, 0, 2, 2]) (w 0 [2, 1, 2, 0])) (by decide)

private theorem basisLaw14 :
    Derives basis
      (w 0 [1, 0, 2, 2])
      (w 2 [0, 1, 0, 2]) :=
  Derives.fromBasis (e :=
    Identity.mk (w 0 [1, 0, 2, 2]) (w 2 [0, 1, 0, 2])) (by decide)

/-! ## Substitution instances of the ten displayed swap laws -/

/-- Law 3: `xxyy = xyxy`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw03 (x y : Word Nat) :
    Derives basis
      (((x ++ x) ++ y) ++ y)
      (((x ++ y) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisLaw03 (instantiateThreeWords x y y)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 4: `xxyy = xyyx`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw04 (x y : Word Nat) :
    Derives basis
      (((x ++ x) ++ y) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisLaw04 (instantiateThreeWords x y y)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 5: `xxyy = yxxy`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw05 (x y : Word Nat) :
    Derives basis
      (((x ++ x) ++ y) ++ y)
      (((y ++ x) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisLaw05 (instantiateThreeWords x y y)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 6: `xxyzy = xyxzy`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw06 (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((x ++ y) ++ x) ++ z) ++ y) := by
  have substituted :=
    Derives.subst basisLaw06 (instantiateThreeWords x y z)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 7: `xxyzy = yxxzy`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw07 (x y z : Word Nat) :
    Derives basis
      ((((x ++ x) ++ y) ++ z) ++ y)
      ((((y ++ x) ++ x) ++ z) ++ y) := by
  have substituted :=
    Derives.subst basisLaw07 (instantiateThreeWords x y z)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 10: `xyxzz = xyzxz`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw10 (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ z) ++ z)
      ((((x ++ y) ++ z) ++ x) ++ z) := by
  have substituted :=
    Derives.subst basisLaw10 (instantiateThreeWords x y z)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 11: `xyxzz = xyzzx`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw11 (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ z) ++ z)
      ((((x ++ y) ++ z) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisLaw11 (instantiateThreeWords x y z)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 12: `xyxzz = xzyxz`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw12 (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ z) ++ z)
      ((((x ++ z) ++ y) ++ x) ++ z) := by
  have substituted :=
    Derives.subst basisLaw12 (instantiateThreeWords x y z)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 13: `xyxzz = xzyzx`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw13 (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ z) ++ z)
      ((((x ++ z) ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisLaw13 (instantiateThreeWords x y z)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Law 14: `xyxzz = zxyxz`, with arbitrary nonempty word substitutions. -/
theorem derivesLaw14 (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ z) ++ z)
      ((((z ++ x) ++ y) ++ x) ++ z) := by
  have substituted :=
    Derives.subst basisLaw14 (instantiateThreeWords x y z)
  simpa [w, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-! ## First-first endpoint swaps

The two displayed occurrences of each exchanged block are ordered
`first x, first y, last x, last y`. The four theorems cover the empty/nonempty
status of the two gaps following `first y` and `last x`.
-/

theorem derivesFirstFirstNoGaps (x y : Word Nat) :
    Derives basis
      (((x ++ y) ++ x) ++ y)
      (((y ++ x) ++ x) ++ y) :=
  (derivesLaw03 x y).symm.trans (derivesLaw05 x y)

theorem derivesFirstFirstRightGap
    (x y rightGap : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ rightGap) ++ y)
      ((((y ++ x) ++ x) ++ rightGap) ++ y) :=
  (derivesLaw06 x y rightGap).symm.trans
    (derivesLaw07 x y rightGap)

theorem derivesFirstFirstLeftGap
    (x y leftGap : Word Nat) :
    Derives basis
      ((((x ++ y) ++ leftGap) ++ x) ++ y)
      ((((y ++ x) ++ leftGap) ++ x) ++ y) :=
  (derivesLaw12 x leftGap y).symm.trans
    (derivesLaw14 x leftGap y)

/-- The two-gap first-first move. The temporary duplicated `x` is introduced
with law 2, the swap is law 7 with the whole middle as `z`, and law 2 removes
the duplicate after the swap. -/
theorem derivesFirstFirstBothGaps
    (x y leftGap rightGap : Word Nat) :
    Derives basis
      (((((x ++ y) ++ leftGap) ++ x) ++ rightGap) ++ y)
      (((((y ++ x) ++ leftGap) ++ x) ++ rightGap) ++ y) := by
  have expand :
      Derives basis
        (((((x ++ y) ++ leftGap) ++ x) ++ rightGap) ++ y)
        ((((((x ++ x) ++ y) ++ leftGap) ++ x) ++ rightGap) ++ y) := by
    have core :=
      Derives.appendRight
        (derivesLeftEndpointExpansion x (y ++ leftGap))
        (rightGap ++ y)
    simpa [Word.append_assoc] using core
  have swap :
      Derives basis
        ((((((x ++ x) ++ y) ++ leftGap) ++ x) ++ rightGap) ++ y)
        ((((((y ++ x) ++ x) ++ leftGap) ++ x) ++ rightGap) ++ y) := by
    simpa [Word.append_assoc] using
      derivesLaw07 x y ((leftGap ++ x) ++ rightGap)
  have contract :
      Derives basis
        ((((((y ++ x) ++ x) ++ leftGap) ++ x) ++ rightGap) ++ y)
        (((((y ++ x) ++ leftGap) ++ x) ++ rightGap) ++ y) := by
    have core :=
      Derives.appendRight
        (Derives.prepend y
          (derivesLeftEndpointExpansion x leftGap).symm)
        (rightGap ++ y)
    simpa [Word.append_assoc] using core
  exact expand.trans (swap.trans contract)

/-! ## Mixed first-last endpoint swaps

Here `first y` and `last x` are adjacent. The move changes
`... first-y, last-x ...` into `... last-x, first-y ...` while the earlier
`first x` and later `last y` remain as guards.
-/

theorem derivesFirstLastNoGaps (x y : Word Nat) :
    Derives basis
      (((x ++ y) ++ x) ++ y)
      (((x ++ x) ++ y) ++ y) :=
  (derivesLaw03 x y).symm

theorem derivesFirstLastRightGap
    (x y rightGap : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ rightGap) ++ y)
      ((((x ++ x) ++ y) ++ rightGap) ++ y) :=
  (derivesLaw06 x y rightGap).symm

theorem derivesFirstLastLeftGap
    (x y leftGap : Word Nat) :
    Derives basis
      ((((x ++ leftGap) ++ y) ++ x) ++ y)
      ((((x ++ leftGap) ++ x) ++ y) ++ y) :=
  (derivesLaw10 x leftGap y).symm

/-- The two-gap mixed move. Law 2 pads the later `y`, law 11 performs the
central exchange, and law 2 removes the padding in the new position. -/
theorem derivesFirstLastBothGaps
    (x y leftGap rightGap : Word Nat) :
    Derives basis
      (((((x ++ leftGap) ++ y) ++ x) ++ rightGap) ++ y)
      (((((x ++ leftGap) ++ x) ++ y) ++ rightGap) ++ y) := by
  have expand :
      Derives basis
        (((((x ++ leftGap) ++ y) ++ x) ++ rightGap) ++ y)
        ((((((x ++ leftGap) ++ y) ++ y) ++ x) ++ rightGap) ++ y) := by
    have core :=
      Derives.prepend (x ++ leftGap)
        (derivesLeftEndpointExpansion y (x ++ rightGap))
    simpa [Word.append_assoc] using core
  have swap :
      Derives basis
        ((((((x ++ leftGap) ++ y) ++ y) ++ x) ++ rightGap) ++ y)
        ((((((x ++ leftGap) ++ x) ++ y) ++ y) ++ rightGap) ++ y) := by
    have core :=
      Derives.appendRight
        (derivesLaw11 x leftGap y).symm
        (rightGap ++ y)
    simpa [Word.append_assoc] using core
  have contract :
      Derives basis
        ((((((x ++ leftGap) ++ x) ++ y) ++ y) ++ rightGap) ++ y)
        (((((x ++ leftGap) ++ x) ++ y) ++ rightGap) ++ y) := by
    have core :=
      Derives.prepend ((x ++ leftGap) ++ x)
        (derivesLeftEndpointExpansion y rightGap).symm
    simpa [Word.append_assoc] using core
  exact expand.trans (swap.trans contract)

/-! ## Last-last endpoint swaps

The first occurrences are ordered `first x, first y`; the adjacent second
occurrences are exchanged. Again the four theorems cover the two gap
boundaries.
-/

theorem derivesLastLastNoGaps (x y : Word Nat) :
    Derives basis
      (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) :=
  (derivesLaw03 x y).symm.trans (derivesLaw04 x y)

theorem derivesLastLastRightGap
    (x y rightGap : Word Nat) :
    Derives basis
      ((((x ++ y) ++ rightGap) ++ x) ++ y)
      ((((x ++ y) ++ rightGap) ++ y) ++ x) :=
  (derivesLaw12 x rightGap y).symm.trans
    (derivesLaw13 x rightGap y)

theorem derivesLastLastLeftGap
    (x y leftGap : Word Nat) :
    Derives basis
      ((((x ++ leftGap) ++ y) ++ x) ++ y)
      ((((x ++ leftGap) ++ y) ++ y) ++ x) :=
  (derivesLaw10 x leftGap y).symm.trans
    (derivesLaw11 x leftGap y)

/-- The two-gap last-last move. Law 8 pads the earlier `x`, reversed law 11
exchanges the guarded endpoints, and reversed law 8 removes the padding. -/
theorem derivesLastLastBothGaps
    (x y leftGap rightGap : Word Nat) :
    Derives basis
      (((((x ++ leftGap) ++ y) ++ rightGap) ++ x) ++ y)
      (((((x ++ leftGap) ++ y) ++ rightGap) ++ y) ++ x) := by
  have expand :
      Derives basis
        (((((x ++ leftGap) ++ y) ++ rightGap) ++ x) ++ y)
        ((((((x ++ leftGap) ++ y) ++ rightGap) ++ x) ++ x) ++ y) := by
    have core :=
      Derives.appendRight
        (derivesRightEndpointExpansion x
          ((leftGap ++ y) ++ rightGap))
        y
    simpa [Word.append_assoc] using core
  have swap :
      Derives basis
        ((((((x ++ leftGap) ++ y) ++ rightGap) ++ x) ++ x) ++ y)
        ((((((x ++ leftGap) ++ y) ++ rightGap) ++ y) ++ x) ++ x) := by
    have core :=
      Derives.prepend (x ++ leftGap)
        (derivesLaw11 y rightGap x).symm
    simpa [Word.append_assoc] using core
  have contract :
      Derives basis
        ((((((x ++ leftGap) ++ y) ++ rightGap) ++ y) ++ x) ++ x)
        (((((x ++ leftGap) ++ y) ++ rightGap) ++ y) ++ x) := by
    simpa [Word.append_assoc] using
      (derivesRightEndpointExpansion x
        (((leftGap ++ y) ++ rightGap) ++ y)).symm
  exact expand.trans (swap.trans contract)

/-! ## List-level gap packages -/

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

/-- Swap adjacent first occurrences when the second `x` occurs before the
second `y`. Both intervening gaps may be empty. -/
theorem listDerivesFirstFirst
    (x y : Nat) (leftGap rightGap : List Nat) :
    ListDerives
      ([x, y] ++ leftGap ++ [x] ++ rightGap ++ [y])
      ([y, x] ++ leftGap ++ [x] ++ rightGap ++ [y]) := by
  cases leftGap with
  | nil =>
      cases rightGap with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
              derivesFirstFirstNoGaps
                (Word.singleton x) (Word.singleton y)
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesFirstFirstRightGap
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons rightHead rightTail)
  | cons leftHead leftTail =>
      cases rightGap with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesFirstFirstLeftGap
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons leftHead leftTail)
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesFirstFirstBothGaps
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

/-- Swap adjacent `first y, last x` endpoints between the guarding
`first x` and `last y`. Both outer gaps may be empty. -/
theorem listDerivesFirstLast
    (x y : Nat) (leftGap rightGap : List Nat) :
    ListDerives
      ([x] ++ leftGap ++ [y, x] ++ rightGap ++ [y])
      ([x] ++ leftGap ++ [x, y] ++ rightGap ++ [y]) := by
  cases leftGap with
  | nil =>
      cases rightGap with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
              derivesFirstLastNoGaps
                (Word.singleton x) (Word.singleton y)
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesFirstLastRightGap
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons rightHead rightTail)
  | cons leftHead leftTail =>
      cases rightGap with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesFirstLastLeftGap
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons leftHead leftTail)
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesFirstLastBothGaps
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

/-- Swap adjacent last occurrences after the ordered first occurrences.
Both intervening gaps may be empty. -/
theorem listDerivesLastLast
    (x y : Nat) (leftGap rightGap : List Nat) :
    ListDerives
      ([x] ++ leftGap ++ [y] ++ rightGap ++ [x, y])
      ([x] ++ leftGap ++ [y] ++ rightGap ++ [y, x]) := by
  cases leftGap with
  | nil =>
      cases rightGap with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
              derivesLastLastNoGaps
                (Word.singleton x) (Word.singleton y)
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesLastLastRightGap
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons rightHead rightTail)
  | cons leftHead leftTail =>
      cases rightGap with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesLastLastLeftGap
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons leftHead leftTail)
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesLastLastBothGaps
                  (Word.singleton x) (Word.singleton y)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

/-! ## Six guarded adjacent endpoint moves -/

theorem listDerivesAdjacentFirstFirstXY
    (pre after leftGap rightGap : List Nat) (x y : Nat) :
    ListDerives
      (pre ++ [x, y] ++ leftGap ++ [x] ++ rightGap ++ [y] ++ after)
      (pre ++ [y, x] ++ leftGap ++ [x] ++ rightGap ++ [y] ++ after) := by
  simpa [List.append_assoc] using
    (listDerivesFirstFirst x y leftGap rightGap).context pre after

theorem listDerivesAdjacentFirstFirstYX
    (pre after leftGap rightGap : List Nat) (x y : Nat) :
    ListDerives
      (pre ++ [x, y] ++ leftGap ++ [y] ++ rightGap ++ [x] ++ after)
      (pre ++ [y, x] ++ leftGap ++ [y] ++ rightGap ++ [x] ++ after) := by
  simpa [List.append_assoc] using
    (listDerivesFirstFirst y x leftGap rightGap).symm.context pre after

theorem listDerivesAdjacentMixedXY
    (before after leftGap rightGap : List Nat) (x y : Nat) :
    ListDerives
      (before ++ [x] ++ leftGap ++ [x, y] ++ rightGap ++ [y] ++ after)
      (before ++ [x] ++ leftGap ++ [y, x] ++ rightGap ++ [y] ++ after) := by
  simpa [List.append_assoc] using
    (listDerivesFirstLast x y leftGap rightGap).symm.context before after

theorem listDerivesAdjacentMixedYX
    (before after leftGap rightGap : List Nat) (x y : Nat) :
    ListDerives
      (before ++ [y] ++ leftGap ++ [x, y] ++ rightGap ++ [x] ++ after)
      (before ++ [y] ++ leftGap ++ [y, x] ++ rightGap ++ [x] ++ after) := by
  simpa [List.append_assoc] using
    (listDerivesFirstLast y x leftGap rightGap).context before after

theorem listDerivesAdjacentLastLastXY
    (before after leftGap rightGap : List Nat) (x y : Nat) :
    ListDerives
      (before ++ [x] ++ leftGap ++ [y] ++ rightGap ++ [x, y] ++ after)
      (before ++ [x] ++ leftGap ++ [y] ++ rightGap ++ [y, x] ++ after) := by
  simpa [List.append_assoc] using
    (listDerivesLastLast x y leftGap rightGap).context before after

theorem listDerivesAdjacentLastLastYX
    (before after leftGap rightGap : List Nat) (x y : Nat) :
    ListDerives
      (before ++ [y] ++ leftGap ++ [x] ++ rightGap ++ [x, y] ++ after)
      (before ++ [y] ++ leftGap ++ [x] ++ rightGap ++ [y, x] ++ after) := by
  simpa [List.append_assoc] using
    (listDerivesLastLast y x leftGap rightGap).symm.context before after

/-- The six possible endpoint types of two adjacent occurrences whose two
letters each occur exactly twice. This is the local contract consumed by an
event-poset normalizer; it contains no global linear-extension argument. -/
inductive AdjacentEndpointPosition
    (x y : Nat) (pre post : List Nat) : Prop
  | firstFirstXY (leftGap rightGap after : List Nat)
      (postShape : post = leftGap ++ x :: (rightGap ++ y :: after))
  | firstFirstYX (leftGap rightGap after : List Nat)
      (postShape : post = leftGap ++ y :: (rightGap ++ x :: after))
  | mixedXY (before leftGap rightGap after : List Nat)
      (preShape : pre = before ++ x :: leftGap)
      (postShape : post = rightGap ++ y :: after)
  | mixedYX (before leftGap rightGap after : List Nat)
      (preShape : pre = before ++ y :: leftGap)
      (postShape : post = rightGap ++ x :: after)
  | lastLastXY (before leftGap rightGap : List Nat)
      (preShape : pre = before ++ x :: (leftGap ++ y :: rightGap))
  | lastLastYX (before leftGap rightGap : List Nat)
      (preShape : pre = before ++ y :: (leftGap ++ x :: rightGap))

/-- Every structurally guarded adjacent endpoint exchange is derivable from
the exact 14-law basis. -/
theorem listDerivesAdjacentOfPosition
    {x y : Nat} {pre post : List Nat}
    (position : AdjacentEndpointPosition x y pre post) :
    ListDerives
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) := by
  cases position with
  | firstFirstXY leftGap rightGap after postShape =>
      subst post
      simpa [List.append_assoc] using
        listDerivesAdjacentFirstFirstXY
          pre after leftGap rightGap x y
  | firstFirstYX leftGap rightGap after postShape =>
      subst post
      simpa [List.append_assoc] using
        listDerivesAdjacentFirstFirstYX
          pre after leftGap rightGap x y
  | mixedXY before leftGap rightGap after preShape postShape =>
      subst pre
      subst post
      simpa [List.append_assoc] using
        listDerivesAdjacentMixedXY
          before after leftGap rightGap x y
  | mixedYX before leftGap rightGap after preShape postShape =>
      subst pre
      subst post
      simpa [List.append_assoc] using
        listDerivesAdjacentMixedYX
          before after leftGap rightGap x y
  | lastLastXY before leftGap rightGap preShape =>
      subst pre
      simpa [List.append_assoc] using
        listDerivesAdjacentLastLastXY
          before post leftGap rightGap x y
  | lastLastYX before leftGap rightGap preShape =>
      subst pre
      simpa [List.append_assoc] using
        listDerivesAdjacentLastLastYX
          before post leftGap rightGap x y

private theorem distinctOccurrencesOrdered
    {letters : List Nat} {x y : Nat}
    (different : x ≠ y) (xMember : x ∈ letters) (yMember : y ∈ letters) :
    (∃ before middle after,
        letters = before ++ x :: (middle ++ y :: after)) ∨
      (∃ before middle after,
        letters = before ++ y :: (middle ++ x :: after)) := by
  rcases List.append_of_mem xMember with
    ⟨xBefore, xAfter, xShape⟩
  rw [xShape] at yMember
  simp only [List.mem_append, List.mem_cons] at yMember
  rcases yMember with yBefore | yAtOrAfter
  · rcases List.append_of_mem yBefore with
      ⟨before, middle, beforeShape⟩
    exact Or.inr ⟨before, middle, xAfter, by
      rw [xShape, beforeShape]
      simp [List.append_assoc]⟩
  · rcases yAtOrAfter with equal | yAfter
    · exact (different equal.symm).elim
    · rcases List.append_of_mem yAfter with
        ⟨middle, after, afterShape⟩
      exact Or.inl ⟨xBefore, middle, after, by
        rw [xShape, afterShape]⟩

/-- Exact quadratic multiplicities force one of the six endpoint-position
guards. -/
theorem adjacentEndpointPositionOfCounts
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xQuadratic : (pre ++ (x :: y :: post)).count x = 2)
    (yQuadratic : (pre ++ (x :: y :: post)).count y = 2) :
    AdjacentEndpointPosition x y pre post := by
  have xSideCounts : pre.count x + post.count x = 1 := by
    have count := xQuadratic
    simp only [List.count_append, List.count_cons_self,
      List.count_cons_of_ne (Ne.symm different)] at count
    omega
  have ySideCounts : pre.count y + post.count y = 1 := by
    have count := yQuadratic
    simp only [List.count_append, List.count_cons_of_ne different,
      List.count_cons_self] at count
    omega
  by_cases xInPre : x ∈ pre
  · by_cases yInPre : y ∈ pre
    · rcases distinctOccurrencesOrdered different xInPre yInPre with
        orderedXY | orderedYX
      · rcases orderedXY with ⟨before, leftGap, rightGap, shape⟩
        exact AdjacentEndpointPosition.lastLastXY
          before leftGap rightGap shape
      · rcases orderedYX with ⟨before, leftGap, rightGap, shape⟩
        exact AdjacentEndpointPosition.lastLastYX
          before leftGap rightGap shape
    · have yPreCount : pre.count y = 0 :=
        List.count_eq_zero.mpr yInPre
      have yInPost : y ∈ post := by
        apply List.count_pos_iff.mp
        omega
      rcases List.append_of_mem xInPre with
        ⟨before, leftGap, preShape⟩
      rcases List.append_of_mem yInPost with
        ⟨rightGap, after, postShape⟩
      exact AdjacentEndpointPosition.mixedXY
        before leftGap rightGap after preShape postShape
  · have xPreCount : pre.count x = 0 :=
      List.count_eq_zero.mpr xInPre
    have xInPost : x ∈ post := by
      apply List.count_pos_iff.mp
      omega
    by_cases yInPre : y ∈ pre
    · rcases List.append_of_mem yInPre with
        ⟨before, leftGap, preShape⟩
      rcases List.append_of_mem xInPost with
        ⟨rightGap, after, postShape⟩
      exact AdjacentEndpointPosition.mixedYX
        before leftGap rightGap after preShape postShape
    · have yPreCount : pre.count y = 0 :=
        List.count_eq_zero.mpr yInPre
      have yInPost : y ∈ post := by
        apply List.count_pos_iff.mp
        omega
      rcases distinctOccurrencesOrdered different xInPost yInPost with
        orderedXY | orderedYX
      · rcases orderedXY with ⟨leftGap, rightGap, after, shape⟩
        exact AdjacentEndpointPosition.firstFirstXY
          leftGap rightGap after shape
      · rcases orderedYX with ⟨leftGap, rightGap, after, shape⟩
        exact AdjacentEndpointPosition.firstFirstYX
          leftGap rightGap after shape

/-- Clean normalizer-facing contract: adjacent occurrences of two distinct
quadratic letters may be exchanged using only the exact displayed basis. -/
theorem listDerivesAdjacentQuadraticSwap
    {x y : Nat} {pre post : List Nat}
    (different : x ≠ y)
    (xQuadratic : (pre ++ (x :: y :: post)).count x = 2)
    (yQuadratic : (pre ++ (x :: y :: post)).count y = 2) :
    ListDerives
      (pre ++ (x :: y :: post))
      (pre ++ (y :: x :: post)) :=
  listDerivesAdjacentOfPosition
    (adjacentEndpointPositionOfCounts
      different xQuadratic yQuadratic)

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

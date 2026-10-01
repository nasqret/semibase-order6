import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op

/-!
# Lee--Zhang Proposition 23.9 moves

This file develops only basis-parameterized syntax for the four published
laws in Proposition 23.9.  In particular, none of the derivations below is
transported from the fixed thirteen-law `S5_402` basis.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9Moves

open SemigroupBasis

/-- The exact four-law basis exposed by the Proposition 23.9 hull. -/
abbrev B4Basis : List (Identity Nat) :=
  SemigroupBasis.Order6Subdirect.Hull23_9_S2_4_S5_402op.publishedBasis

/-- The published power law `x^3 = x^2`, as an identity over `Nat`. -/
def powerLaw : Identity Nat :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0]⟩⟩

/-- The published left sandwich law `x^2 y x = x y x`. -/
def leftSandwichLaw : Identity Nat :=
  ⟨⟨0, [0, 1, 0]⟩, ⟨0, [1, 0]⟩⟩

/-- The published right sandwich law `x y x^2 = x y x`. -/
def rightSandwichLaw : Identity Nat :=
  ⟨⟨0, [1, 0, 0]⟩, ⟨0, [1, 0]⟩⟩

/-- The concrete long law `h x^2 k y^2 t z^2 = h y^2 t x^2 k z^2`. -/
def longBlockSwapLaw : Identity Nat :=
  ⟨⟨0, [1, 1, 2, 3, 3, 4, 5, 5]⟩,
    ⟨0, [3, 3, 4, 1, 1, 2, 5, 5]⟩⟩

theorem powerLaw_mem_publishedBasis :
    powerLaw ∈ B4Basis := by
  decide

theorem leftSandwichLaw_mem_publishedBasis :
    leftSandwichLaw ∈ B4Basis := by
  decide

theorem rightSandwichLaw_mem_publishedBasis :
    rightSandwichLaw ∈ B4Basis := by
  decide

theorem longBlockSwapLaw_mem_publishedBasis :
    longBlockSwapLaw ∈ B4Basis := by
  decide

/-- The generic list congruence, specialized only to the published B4 list. -/
abbrev B4ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives B4Basis

private def instantiateSixWords
    (h x k y t z : Word Nat) : Nat → Word Nat
  | 0 => h
  | 1 => x
  | 2 => k
  | 3 => y
  | 4 => t
  | 5 => z
  | n + 6 => Word.singleton (n + 6)

/-- Generic substitution instance of `x^3 = x^2`. -/
theorem derivesPowerContraction (x : Word Nat) :
    Derives B4Basis ((x ++ x) ++ x) (x ++ x) := by
  have substituted :=
    Derives.subst
      (Derives.fromBasis (e := powerLaw)
        powerLaw_mem_publishedBasis)
      (instantiateSixWords x x x x x x)
  simpa [powerLaw, instantiateSixWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x^2 y x = x y x`. -/
theorem derivesLeftSandwichContraction (x y : Word Nat) :
    Derives B4Basis (((x ++ x) ++ y) ++ x) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst
      (Derives.fromBasis (e := leftSandwichLaw)
        leftSandwichLaw_mem_publishedBasis)
      (instantiateSixWords x y x x x x)
  simpa [leftSandwichLaw, instantiateSixWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of `x y x^2 = x y x`. -/
theorem derivesRightSandwichContraction (x y : Word Nat) :
    Derives B4Basis (((x ++ y) ++ x) ++ x) ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst
      (Derives.fromBasis (e := rightSandwichLaw)
        rightSandwichLaw_mem_publishedBasis)
      (instantiateSixWords x y x x x x)
  simpa [rightSandwichLaw, instantiateSixWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Generic substitution instance of the concrete six-variable long law. -/
theorem derivesLongBlockSwap
    (h x k y t z : Word Nat) :
    Derives B4Basis
      ((((((((h ++ x) ++ x) ++ k) ++ y) ++ y) ++ t) ++ z) ++ z)
      ((((((((h ++ y) ++ y) ++ t) ++ x) ++ x) ++ k) ++ z) ++ z) := by
  have substituted :=
    Derives.subst
      (Derives.fromBasis (e := longBlockSwapLaw)
        longBlockSwapLaw_mem_publishedBasis)
      (instantiateSixWords h x k y t z)
  simpa [longBlockSwapLaw, instantiateSixWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Eliminate the optional `k` separator from the displayed long law.
The concrete law is used with `k := x`; the resulting cubes are expanded
and contracted with the first B4 law. -/
theorem derivesLongBlockSwapWithoutK
    (h x y t z : Word Nat) :
    Derives B4Basis
      (((((((h ++ x) ++ x) ++ y) ++ y) ++ t) ++ z) ++ z)
      (((((((h ++ y) ++ y) ++ t) ++ x) ++ x) ++ z) ++ z) := by
  have expandXCore := (derivesPowerContraction x).symm
  have expandX :=
    Derives.appendRight (Derives.prepend h expandXCore)
      ((((y ++ y) ++ t) ++ z) ++ z)
  have swap := derivesLongBlockSwap h x x y t z
  have contractX :=
    Derives.appendRight
      (Derives.prepend (((h ++ y) ++ y) ++ t)
        (derivesPowerContraction x)) (z ++ z)
  have expandX' :
      Derives B4Basis
        (((((((h ++ x) ++ x) ++ y) ++ y) ++ t) ++ z) ++ z)
        ((((((((h ++ x) ++ x) ++ x) ++ y) ++ y) ++ t) ++ z) ++ z) := by
    simpa [Word.append_assoc] using expandX
  have contractX' :
      Derives B4Basis
        ((((((((h ++ y) ++ y) ++ t) ++ x) ++ x) ++ x) ++ z) ++ z)
        (((((((h ++ y) ++ y) ++ t) ++ x) ++ x) ++ z) ++ z) := by
    simpa [Word.append_assoc] using contractX
  exact expandX'.trans <| swap.trans contractX'

/-- Eliminate the optional `t` separator from the displayed long law by
using `t := y` and cancelling the resulting cubes. -/
theorem derivesLongBlockSwapWithoutT
    (h x k y z : Word Nat) :
    Derives B4Basis
      (((((((h ++ x) ++ x) ++ k) ++ y) ++ y) ++ z) ++ z)
      (((((((h ++ y) ++ y) ++ x) ++ x) ++ k) ++ z) ++ z) := by
  have expandY :=
    Derives.appendRight
      (Derives.prepend (((h ++ x) ++ x) ++ k)
        (derivesPowerContraction y).symm) (z ++ z)
  have swap := derivesLongBlockSwap h x k y y z
  have contractY :=
    Derives.appendRight (Derives.prepend h (derivesPowerContraction y))
      ((((x ++ x) ++ k) ++ z) ++ z)
  have expandY' :
      Derives B4Basis
        (((((((h ++ x) ++ x) ++ k) ++ y) ++ y) ++ z) ++ z)
        ((((((((h ++ x) ++ x) ++ k) ++ y) ++ y) ++ y) ++ z) ++ z) := by
    simpa [Word.append_assoc] using expandY
  have contractY' :
      Derives B4Basis
        ((((((((h ++ y) ++ y) ++ y) ++ x) ++ x) ++ k) ++ z) ++ z)
        (((((((h ++ y) ++ y) ++ x) ++ x) ++ k) ++ z) ++ z) := by
    simpa [Word.append_assoc] using contractY
  exact expandY'.trans <| swap.trans contractY'

/-- Eliminate both optional middle separators from the displayed long law.
This is the `k := x`, `t := y` instance bracketed by power moves. -/
theorem derivesLongBlockSwapWithoutKOrT
    (h x y z : Word Nat) :
    Derives B4Basis
      ((((((h ++ x) ++ x) ++ y) ++ y) ++ z) ++ z)
      ((((((h ++ y) ++ y) ++ x) ++ x) ++ z) ++ z) := by
  have expandX :=
    Derives.appendRight
      (Derives.prepend h (derivesPowerContraction x).symm)
      (((y ++ y) ++ z) ++ z)
  have expandY :=
    Derives.appendRight
      (Derives.prepend (((h ++ x) ++ x) ++ x)
        (derivesPowerContraction y).symm) (z ++ z)
  have swap := derivesLongBlockSwap h x x y y z
  have contractY :=
    Derives.appendRight (Derives.prepend h (derivesPowerContraction y))
      ((((x ++ x) ++ x) ++ z) ++ z)
  have contractX :=
    Derives.appendRight
      (Derives.prepend ((h ++ y) ++ y)
        (derivesPowerContraction x)) (z ++ z)
  have expandX' :
      Derives B4Basis
        ((((((h ++ x) ++ x) ++ y) ++ y) ++ z) ++ z)
        (((((((h ++ x) ++ x) ++ x) ++ y) ++ y) ++ z) ++ z) := by
    simpa [Word.append_assoc] using expandX
  have expandY' :
      Derives B4Basis
        (((((((h ++ x) ++ x) ++ x) ++ y) ++ y) ++ z) ++ z)
        ((((((((h ++ x) ++ x) ++ x) ++ y) ++ y) ++ y) ++ z) ++ z) := by
    simpa [Word.append_assoc] using expandY
  have contractY' :
      Derives B4Basis
        ((((((((h ++ y) ++ y) ++ y) ++ x) ++ x) ++ x) ++ z) ++ z)
        (((((((h ++ y) ++ y) ++ x) ++ x) ++ x) ++ z) ++ z) := by
    simpa [Word.append_assoc] using contractY
  have contractX' :
      Derives B4Basis
        (((((((h ++ y) ++ y) ++ x) ++ x) ++ x) ++ z) ++ z)
        ((((((h ++ y) ++ y) ++ x) ++ x) ++ z) ++ z) := by
    simpa [Word.append_assoc] using contractX
  exact
    expandX'.trans <| expandY'.trans <|
      swap.trans <| contractY'.trans contractX'

/-- Expand the left displayed occurrence of a repeated letter. -/
theorem listDerivesExpandLeftOccurrence (x : Nat) :
    ∀ middle : List Nat,
      B4ListDerives
        ([x] ++ middle ++ [x])
        ([x, x] ++ middle ++ [x])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesPowerContraction (Word.singleton x))).symm
  | head :: tail => by
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesLeftSandwichContraction
            (Word.singleton x)
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail))).symm

/-- Expand the right displayed occurrence of a repeated letter. -/
theorem listDerivesExpandRightOccurrence (x : Nat) :
    ∀ middle : List Nat,
      B4ListDerives
        ([x] ++ middle ++ [x])
        ([x] ++ middle ++ [x, x])
  | [] => by
      simpa [Word.singleton, Word.append] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesPowerContraction (Word.singleton x))).symm
  | head :: tail => by
      simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
        Word.singleton, Word.append, List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesRightSandwichContraction
            (Word.singleton x)
            (SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail))).symm

/-- Duplicate one selected occurrence of a globally repeated letter.  The
other occurrence is allowed on either side of the selected one. -/
theorem listDerivesDuplicateSelectedOccurrence
    (x : Nat) (before after : List Nat)
    (multiple : 2 ≤ (before ++ [x] ++ after).count x) :
    B4ListDerives
      (before ++ [x] ++ after)
      (before ++ [x, x] ++ after) := by
  by_cases afterMember : x ∈ after
  · obtain ⟨middle, suffix, split⟩ :=
      List.mem_iff_append.mp afterMember
    have expanded :=
      (listDerivesExpandLeftOccurrence x middle).context
        before suffix
    simpa [split, List.append_assoc] using expanded
  · have beforeMember : x ∈ before := by
      apply Classical.byContradiction
      intro beforeAbsent
      have beforeZero : before.count x = 0 :=
        List.count_eq_zero.mpr beforeAbsent
      have afterZero : after.count x = 0 :=
        List.count_eq_zero.mpr afterMember
      have countOne :
          (before ++ [x] ++ after).count x = 1 := by
        simp [List.count_append, beforeZero, afterZero]
      rw [countOne] at multiple
      omega
    obtain ⟨beforePrefix, middle, split⟩ :=
      List.mem_iff_append.mp beforeMember
    have expanded :=
      (listDerivesExpandRightOccurrence x middle).context
        beforePrefix after
    simpa [split, List.append_assoc] using expanded

private theorem count_le_duplicateSelected
    (inserted tested : Nat) (before after : List Nat) :
    (before ++ [inserted] ++ after).count tested ≤
      (before ++ [inserted, inserted] ++ after).count tested := by
  by_cases equal : inserted = tested
  · subst inserted
    simp [List.count_append]
  · simp [List.count_append, equal]

private theorem listDerivesExpandThreeBlockHeads
    (h x y z : Word Nat)
    (xMultiple : 2 ≤ ((((h ++ x) ++ y) ++ z).toList.count x.head))
    (yMultiple : 2 ≤ ((((h ++ x) ++ y) ++ z).toList.count y.head))
    (zMultiple : 2 ≤ ((((h ++ x) ++ y) ++ z).toList.count z.head)) :
    B4ListDerives
      (((h ++ x) ++ y) ++ z).toList
      (h.toList ++ [x.head, x.head] ++ x.tail ++
        [y.head, y.head] ++ y.tail ++
        [z.head, z.head] ++ z.tail) := by
  have explicitXMultiple :
      2 ≤
        (h.toList ++ [x.head] ++
          (x.tail ++ y.toList ++ z.toList)).count x.head := by
    simpa [Word.toList, Word.toList_append, List.append_assoc] using
      xMultiple
  have expandX :=
    listDerivesDuplicateSelectedOccurrence
      x.head h.toList (x.tail ++ y.toList ++ z.toList)
      explicitXMultiple

  have originalYMultiple :
      2 ≤
        (h.toList ++ [x.head] ++
          (x.tail ++ y.toList ++ z.toList)).count y.head := by
    simpa [Word.toList, Word.toList_append, List.append_assoc] using
      yMultiple
  have afterXMultipleY :
      2 ≤
        (h.toList ++ [x.head, x.head] ++
          (x.tail ++ y.toList ++ z.toList)).count y.head :=
    Nat.le_trans originalYMultiple <|
      count_le_duplicateSelected
        x.head y.head h.toList (x.tail ++ y.toList ++ z.toList)
  have explicitYMultiple :
      2 ≤
        ((h.toList ++ [x.head, x.head] ++ x.tail) ++
          [y.head] ++ (y.tail ++ z.toList)).count y.head := by
    simpa [Word.toList, List.append_assoc] using afterXMultipleY
  have expandY :=
    listDerivesDuplicateSelectedOccurrence
      y.head (h.toList ++ [x.head, x.head] ++ x.tail)
      (y.tail ++ z.toList) explicitYMultiple

  have originalZMultiple :
      2 ≤
        (h.toList ++ [x.head] ++
          (x.tail ++ y.toList ++ z.toList)).count z.head := by
    simpa [Word.toList, Word.toList_append, List.append_assoc] using
      zMultiple
  have afterXMultipleZ :
      2 ≤
        (h.toList ++ [x.head, x.head] ++
          (x.tail ++ y.toList ++ z.toList)).count z.head :=
    Nat.le_trans originalZMultiple <|
      count_le_duplicateSelected
        x.head z.head h.toList (x.tail ++ y.toList ++ z.toList)
  have afterXYMultipleZ :
      2 ≤
        ((h.toList ++ [x.head, x.head] ++ x.tail) ++
          [y.head, y.head] ++ (y.tail ++ z.toList)).count z.head := by
    have increaseY :=
      count_le_duplicateSelected y.head z.head
        (h.toList ++ [x.head, x.head] ++ x.tail)
        (y.tail ++ z.toList)
    exact Nat.le_trans
      (by
        simpa [Word.toList, List.append_assoc] using
          afterXMultipleZ)
      increaseY
  have explicitZMultiple :
      2 ≤
        ((h.toList ++ [x.head, x.head] ++ x.tail ++
            [y.head, y.head] ++ y.tail) ++
          [z.head] ++ z.tail).count z.head := by
    simpa [Word.toList, List.append_assoc] using afterXYMultipleZ
  have expandZ :=
    listDerivesDuplicateSelectedOccurrence
      z.head
      (h.toList ++ [x.head, x.head] ++ x.tail ++
        [y.head, y.head] ++ y.tail)
      z.tail explicitZMultiple

  have firstStep :
      B4ListDerives
        (((h ++ x) ++ y) ++ z).toList
        (h.toList ++ [x.head, x.head] ++ x.tail ++
          y.toList ++ z.toList) := by
    simpa [Word.toList, Word.toList_append, List.append_assoc] using expandX
  have secondStep :
      B4ListDerives
        (h.toList ++ [x.head, x.head] ++ x.tail ++
          y.toList ++ z.toList)
        (h.toList ++ [x.head, x.head] ++ x.tail ++
          [y.head, y.head] ++ y.tail ++ z.toList) := by
    simpa [Word.toList, List.append_assoc] using expandY
  have thirdStep :
      B4ListDerives
        (h.toList ++ [x.head, x.head] ++ x.tail ++
          [y.head, y.head] ++ y.tail ++ z.toList)
        (h.toList ++ [x.head, x.head] ++ x.tail ++
          [y.head, y.head] ++ y.tail ++
          [z.head, z.head] ++ z.tail) := by
    simpa [Word.toList, List.append_assoc] using expandZ
  exact firstStep.trans (secondStep.trans thirdStep)

private theorem listDerivesExpandedHeadBlockSwap
    (h x y z : Word Nat) :
    B4ListDerives
      (h.toList ++ [x.head, x.head] ++ x.tail ++
        [y.head, y.head] ++ y.tail ++
        [z.head, z.head] ++ z.tail)
      (h.toList ++ [y.head, y.head] ++ y.tail ++
        [x.head, x.head] ++ x.tail ++
        [z.head, z.head] ++ z.tail) := by
  cases x.tail with
  | nil =>
      cases y.tail with
      | nil =>
          have swapped :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesLongBlockSwapWithoutKOrT h
                (Word.singleton x.head) (Word.singleton y.head)
                (Word.singleton z.head)
          simpa [Word.toList, Word.toList_append, Word.singleton,
            List.append_assoc] using swapped.append z.tail
      | cons yTailHead yTailTail =>
          let t :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              yTailHead yTailTail
          have swapped :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesLongBlockSwapWithoutK h
                (Word.singleton x.head) (Word.singleton y.head) t
                (Word.singleton z.head)
          simpa [t, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList, Word.toList_append, Word.singleton,
            List.append_assoc] using swapped.append z.tail
  | cons xTailHead xTailTail =>
      let k :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          xTailHead xTailTail
      cases y.tail with
      | nil =>
          have swapped :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesLongBlockSwapWithoutT h
                (Word.singleton x.head) k (Word.singleton y.head)
                (Word.singleton z.head)
          simpa [k, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList, Word.toList_append, Word.singleton,
            List.append_assoc] using swapped.append z.tail
      | cons yTailHead yTailTail =>
          let t :=
            SemigroupBasis.CoRoots.S5_107.listWordOfCons
              yTailHead yTailTail
          have swapped :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord <|
              derivesLongBlockSwap h
                (Word.singleton x.head) k (Word.singleton y.head) t
                (Word.singleton z.head)
          simpa [k, t, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList, Word.toList_append, Word.singleton,
            List.append_assoc] using swapped.append z.tail

private theorem fourBlockSwap_count_eq
    (h x y z : Word Nat) (tested : Nat) :
    ((((h ++ x) ++ y) ++ z).toList.count tested) =
      ((((h ++ y) ++ x) ++ z).toList.count tested) := by
  simp only [Word.toList_append, List.count_append]
  omega

/-- Lee--Zhang Lemma 23.10.  If the heads of the three displayed blocks are
globally non-simple in `hxyz`, B4 derives the adjacent block transposition
`hxyz = hyxz`. -/
theorem derivesLeeZhang23_10BlockSwap
    (h x y z : Word Nat)
    (xNonSimple : 2 ≤ ((((h ++ x) ++ y) ++ z).toList.count x.head))
    (yNonSimple : 2 ≤ ((((h ++ x) ++ y) ++ z).toList.count y.head))
    (zNonSimple : 2 ≤ ((((h ++ x) ++ y) ++ z).toList.count z.head)) :
    Derives B4Basis
      (((h ++ x) ++ y) ++ z)
      (((h ++ y) ++ x) ++ z) := by
  have expandSource :=
    listDerivesExpandThreeBlockHeads h x y z
      xNonSimple yNonSimple zNonSimple
  have swapExpanded := listDerivesExpandedHeadBlockSwap h x y z
  have targetYNonSimple :
      2 ≤ ((((h ++ y) ++ x) ++ z).toList.count y.head) := by
    rw [← fourBlockSwap_count_eq h x y z y.head]
    exact yNonSimple
  have targetXNonSimple :
      2 ≤ ((((h ++ y) ++ x) ++ z).toList.count x.head) := by
    rw [← fourBlockSwap_count_eq h x y z x.head]
    exact xNonSimple
  have targetZNonSimple :
      2 ≤ ((((h ++ y) ++ x) ++ z).toList.count z.head) := by
    rw [← fourBlockSwap_count_eq h x y z z.head]
    exact zNonSimple
  have expandTarget :=
    listDerivesExpandThreeBlockHeads h y x z
      targetYNonSimple targetXNonSimple targetZNonSimple
  have listDerivation :
      B4ListDerives
        (((h ++ x) ++ y) ++ z).toList
        (((h ++ y) ++ x) ++ z).toList :=
    expandSource.trans <| swapExpanded.trans expandTarget.symm
  cases h with
  | mk hHead hTail =>
      cases x with
      | mk xHead xTail =>
          cases y with
          | mk yHead yTail =>
              cases z with
              | mk zHead zTail =>
                  exact
                    SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
                      listDerivation

end SemigroupBasis.CoRoots.Order6LeeZhang23_9Moves

import SemigroupBasis.CoRoots.Order6SporadicSection15Derivations

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-- Convert a possibly empty list context into the optional nonempty word
used by the expanded Section 15 laws. -/
private def optionalWordOfList : List Nat → Option (Word Nat)
  | [] => none
  | head :: tail => some (S5_107.listWordOfCons head tail)

@[simp]
private theorem appendOptional_optionalWordOfList_toList
    (stem : Word Nat) (letters : List Nat) :
    (appendOptional stem (optionalWordOfList letters)).toList =
      stem.toList ++ letters := by
  cases letters with
  | nil =>
      simp [optionalWordOfList, appendOptional]
  | cons head tail =>
      simp [optionalWordOfList, appendOptional,
        S5_107.listWordOfCons, Word.toList]

@[simp]
private theorem appendOptional_optionalWordOfList_head_tail_append
    (stem : Word Nat) (letters after : List Nat) :
    (appendOptional stem (optionalWordOfList letters)).head ::
        ((appendOptional stem (optionalWordOfList letters)).tail ++ after) =
      stem.head :: (stem.tail ++ letters ++ after) := by
  cases letters with
  | nil =>
      simp [optionalWordOfList, appendOptional]
  | cons head tail =>
      simp [optionalWordOfList, appendOptional,
        S5_107.listWordOfCons, List.append_assoc]

/-! ## Typed list instances of the primitive moves -/

private theorem listDerives15_1aLeft
    (before after : List Nat) (x : Nat) (h k : List Nat) :
    ListDerives
      (before ++ [x, x] ++ h ++ [x] ++ k ++ [x] ++ after)
      (before ++ [x] ++ h ++ [x] ++ k ++ [x] ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    derives15_1aLeft (Word.singleton x)
      (optionalWordOfList h) (optionalWordOfList k)
  simpa [pattern15_1aLeft, pattern15_1aCore,
    Word.toList, Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

private theorem listDerives15_1aRight
    (before after : List Nat) (x : Nat) (h k : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [x, x] ++ after)
      (before ++ [x] ++ h ++ [x] ++ k ++ [x] ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    derives15_1aRight (Word.singleton x)
      (optionalWordOfList h) (optionalWordOfList k)
  simpa [pattern15_1aRight, pattern15_1aCore,
    Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

private theorem listDerives15_1bLeft
    (before after : List Nat) (x y : Nat)
    (h k t : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y] ++ after)
      (before ++ [y] ++ h ++ [x] ++ k ++ [x] ++ t ++ [y] ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    derives15_1bLeft (Word.singleton x) (Word.singleton y)
      (optionalWordOfList h) (optionalWordOfList k)
      (optionalWordOfList t)
  simpa [pattern15_1bSource, pattern15_1bLeftTarget,
    Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

private theorem listDerives15_1cLeft
    (before after : List Nat) (x y hHead : Nat)
    (hTail k : List Nat) :
    ListDerives
      (before ++ [x, x] ++ (hHead :: hTail) ++
        [y] ++ k ++ [y] ++ after)
      (before ++ [x] ++ (hHead :: hTail) ++
        [x, y] ++ k ++ [y] ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    derives15_1cLeft (Word.singleton x) (Word.singleton y)
      (S5_107.listWordOfCons hHead hTail) (optionalWordOfList k)
  simpa [pattern15_1cLeftSource, pattern15_1cLeftTarget,
    S5_107.listWordOfCons, Word.toList, Word.toList_append,
    List.append_assoc] using
      S5_107.ListDerives.context before after core

private theorem listDerives15_1dLeft
    (before after : List Nat) (x y kHead : Nat)
    (h kTail : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++
        (kHead :: kTail) ++ [y, y] ++ after)
      (before ++ [x] ++ h ++ [x, y] ++
        (kHead :: kTail) ++ [y] ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    derives15_1dLeft (Word.singleton x) (Word.singleton y)
      (S5_107.listWordOfCons kHead kTail) (optionalWordOfList h)
  simpa [pattern15_1dLeftSource, pattern15_1dLeftTarget,
    S5_107.listWordOfCons, Word.toList, Word.toList_append,
    List.append_assoc] using
      S5_107.ListDerives.context before after core

/-! ## Power capping -/

/-- One contextual contraction `x^4 -> x^3`, the empty-context instance of
the left law in (15.1a). -/
theorem listDerivesPowerContract
    (before after : List Nat) (x : Nat) :
    ListDerives
      (before ++ [x, x, x, x] ++ after)
      (before ++ [x, x, x] ++ after) := by
  simpa [List.append_assoc] using
    (listDerives15_1aLeft before after x [] [])

/-- The exponent-three cap used in Lemma 15.4. Counts below three are left
unchanged; every adjacent run of length at least three contracts to a cube. -/
def capThree (count : Nat) : Nat :=
  if count < 3 then count else 3

/-- Contract an adjacent power to its exponent-three cap. This theorem makes
no claim about separated occurrences. -/
theorem listDerivesCapRunThree
    (before after : List Nat) (x : Nat) :
    ∀ count,
      ListDerives
        (before ++ List.replicate count x ++ after)
        (before ++ List.replicate (capThree count) x ++ after)
  | 0 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := basis) (before ++ after))
  | 1 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [x] ++ after))
  | 2 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [x, x] ++ after))
  | 3 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := basis)
          (before ++ [x, x, x] ++ after))
  | count + 4 => by
      have first :
          ListDerives
            (before ++ List.replicate (count + 4) x ++ after)
            (before ++ List.replicate (count + 3) x ++ after) := by
        simpa [List.replicate_succ, List.append_assoc] using
          listDerivesPowerContract before
            (List.replicate count x ++ after) x
      exact first.trans
        (listDerivesCapRunThree before after x (count + 3))

/-- Reverse the capped derivation when Lemma 15.4 needs extra displayed
copies of a high-count letter. -/
theorem listDerivesExpandRunFromCapThree
    (before after : List Nat) (x count : Nat) :
    ListDerives
      (before ++ List.replicate (capThree count) x ++ after)
      (before ++ List.replicate count x ++ after) :=
  (listDerivesCapRunThree before after x count).symm

/-! ## One-step high-marker propagation -/

/-- Propagate one additional copy of `high` to the right across a nonempty
factor. The three displayed copies of `high` justify expansion by (15.1a),
and the two displayed copies of `neighbor` justify the (15.1c) move. The
theorem deliberately records the resulting extra `high` occurrence. -/
theorem listDerivesPropagateHighRight
    (before highGapOne highGapTwo neighborGap after : List Nat)
    (high neighbor crossingHead : Nat) (crossingTail : List Nat) :
    ListDerives
      (before ++ [high] ++ highGapOne ++ [high] ++ highGapTwo ++
        [high] ++ (crossingHead :: crossingTail) ++
        [neighbor] ++ neighborGap ++ [neighbor] ++ after)
      (before ++ [high] ++ highGapOne ++ [high] ++ highGapTwo ++
        [high] ++ (crossingHead :: crossingTail) ++
        [high, neighbor] ++ neighborGap ++ [neighbor] ++ after) := by
  have expanded :=
    (listDerives15_1aRight before
      ((crossingHead :: crossingTail) ++ [neighbor] ++
        neighborGap ++ [neighbor] ++ after)
      high highGapOne highGapTwo).symm
  have moved :=
    listDerives15_1cLeft
      (before ++ [high] ++ highGapOne ++ [high] ++ highGapTwo)
      after high neighbor crossingHead crossingTail neighborGap
  have derivation := expanded.trans <| by
    simpa [List.append_assoc] using moved
  simpa [List.append_assoc] using derivation

/-- The leftward dual propagation step. The nonempty `crossing` word is
encoded by `crossingHead :: crossingTail`; the displayed duplicate neighbor
and high-marker cube are exactly the anchors used by (15.1d) and (15.1a). -/
theorem listDerivesPropagateHighLeft
    (before neighborGap highGapOne highGapTwo after : List Nat)
    (neighbor high crossingHead : Nat) (crossingTail : List Nat) :
    ListDerives
      (before ++ [neighbor] ++ neighborGap ++ [neighbor] ++
        (crossingHead :: crossingTail) ++
        [high] ++ highGapOne ++ [high] ++ highGapTwo ++ [high] ++ after)
      (before ++ [neighbor] ++ neighborGap ++ [neighbor, high] ++
        (crossingHead :: crossingTail) ++
        [high] ++ highGapOne ++ [high] ++ highGapTwo ++ [high] ++ after) := by
  have expanded :=
    (listDerives15_1aLeft
      (before ++ [neighbor] ++ neighborGap ++ [neighbor] ++
        (crossingHead :: crossingTail))
      after high highGapOne highGapTwo).symm
  have moved :=
    listDerives15_1dLeft before
      (highGapOne ++ [high] ++ highGapTwo ++ [high] ++ after)
      neighbor high crossingHead neighborGap crossingTail
  have derivation := expanded.trans <| by
    simpa [List.append_assoc] using moved
  simpa [List.append_assoc] using derivation

/-! ## The doubled-letter shuttle -/

/-- Move one displayed occurrence of `doubled` left across an anchor cube and
the following factor. This is the paper's `(15.1a)-(15.1b)-(15.1a)` shuttle:
expand the first cube, apply the left placement of (15.1b), then contract the
four adjacent anchor copies at the next cube. The final displayed `doubled`
copy is the second anchor required by (15.1b); no global multiplicity claim is
made here. -/
theorem listDerivesShuttleDoubledLeft
    (before firstTail betweenSecondCopy after : List Nat)
    (anchor doubled : Nat) :
    ListDerives
      (before ++ [anchor, anchor, anchor] ++ firstTail ++
        [doubled] ++ [anchor, anchor, anchor] ++
        betweenSecondCopy ++ [doubled] ++ after)
      (before ++ [doubled] ++ [anchor, anchor, anchor] ++ firstTail ++
        [anchor, anchor, anchor] ++
        betweenSecondCopy ++ [doubled] ++ after) := by
  have expanded :=
    (listDerivesPowerContract before
      (firstTail ++ [doubled] ++ [anchor, anchor, anchor] ++
        betweenSecondCopy ++ [doubled] ++ after)
      anchor).symm
  have exchanged :=
    listDerives15_1bLeft before after anchor doubled
      ([anchor, anchor, anchor] ++ firstTail) []
      ([anchor, anchor] ++ betweenSecondCopy)
  have contracted :=
    listDerivesPowerContract
      (before ++ [doubled] ++ [anchor, anchor, anchor] ++ firstTail)
      (betweenSecondCopy ++ [doubled] ++ after) anchor
  have exchangedThenContracted := exchanged.trans <| by
    simpa [List.append_assoc] using contracted
  have derivation := expanded.trans <| by
    simpa [List.append_assoc] using exchangedThenContracted
  simpa [List.append_assoc] using derivation

/-! ## Unit permutation under the beta anchor -/

/-- Swap two nonempty units between three copies of the same nonempty anchor
word by (15.1f). In Lemma 15.4 the anchor is instantiated by the nonempty cube
product `y = y₁³ ... yₙ³`, and the two units come from globally simple
runs. The equational move itself is valid for arbitrary nonempty units, so no
unused ambient simplicity hypothesis is imposed here. -/
theorem listDerivesSwapSimpleRunUnitsUnderNonemptyAnchor
    (before after : List Nat)
    (anchorHead unitOneHead unitTwoHead : Nat)
    (anchorTail unitOneTail unitTwoTail : List Nat) :
    ListDerives
      (before ++ (anchorHead :: anchorTail) ++
        (unitOneHead :: unitOneTail) ++ (anchorHead :: anchorTail) ++
        (unitTwoHead :: unitTwoTail) ++ (anchorHead :: anchorTail) ++ after)
      (before ++ (anchorHead :: anchorTail) ++
        (unitTwoHead :: unitTwoTail) ++ (anchorHead :: anchorTail) ++
        (unitOneHead :: unitOneTail) ++ (anchorHead :: anchorTail) ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    derives15_1f
      (S5_107.listWordOfCons unitOneHead unitOneTail)
      (S5_107.listWordOfCons unitTwoHead unitTwoTail)
      (S5_107.listWordOfCons anchorHead anchorTail)
  simpa [pattern15_1fLeft, pattern15_1fRight,
    S5_107.listWordOfCons, Word.toList, Word.toList_append,
    List.append_assoc] using
      S5_107.ListDerives.context before after core

end SemigroupBasis.CoRoots.Order6SporadicSection15

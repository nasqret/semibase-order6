import SemigroupBasis.CoRoots.Order6SporadicSection16BlockNormalization

/-!
The last two transformations in Lee and Zhang (2015), Lemma 16.3, p.51.
A redundant anchor-square separator is removed when either neighbouring
letter block is doubled. At the final boundary only the left neighbour is
tested; a final separator after a simple letter is retained, as required
by Case 1 of the proof of Proposition 16.1 on p.52.
-/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

private theorem fourthPower (anchor : Nat) :
    ListDerives [anchor, anchor, anchor, anchor] [anchor, anchor] := by
  have first : ListDerives [anchor, anchor, anchor, anchor] [anchor, anchor, anchor] :=
    (listPower anchor).append [anchor]
  exact first.trans (listPower anchor)

/-- Remove the separator following a doubled letter block by two applications
of (16.1c) and a final fourth-power contraction. -/
theorem eraseMarkerAfterDoubled (anchor letter : Nat) (gap : List Nat) :
    ListDerives ([anchor, anchor] ++ gap ++ [letter, letter, anchor, anchor])
      ([anchor, anchor] ++ gap ++ [letter, letter]) := by
  have first :
      ListDerives ([anchor, anchor] ++ gap ++ [letter, letter, anchor, anchor])
        ([anchor, anchor, anchor] ++ gap ++ [letter, letter, anchor]) := by
    simpa [List.append_assoc] using ((moveAnchor anchor letter gap).symm.prepend [anchor]).append [anchor]
  have second :
      ListDerives ([anchor, anchor, anchor] ++ gap ++ [letter, letter, anchor])
        ([anchor, anchor, anchor, anchor] ++ gap ++ [letter, letter]) := by
    simpa [List.append_assoc] using (moveAnchor anchor letter gap).symm.prepend [anchor, anchor]
  have third :
      ListDerives ([anchor, anchor, anchor, anchor] ++ gap ++ [letter, letter])
        ([anchor, anchor] ++ gap ++ [letter, letter]) := by
    simpa [List.append_assoc] using (fourthPower anchor).append (gap ++ [letter, letter])
  exact first.trans (second.trans third)

/-- Remove the separator immediately before a doubled letter block. -/
theorem eraseMarkerBeforeDoubled (anchor letter : Nat) (gap : List Nat) :
    ListDerives ([anchor, anchor] ++ gap ++ [anchor, anchor, letter, letter])
      ([anchor, anchor] ++ gap ++ [letter, letter]) := by
  have earlier : SquareSeen anchor ([anchor, anchor] ++ gap) := ⟨[], gap, rfl⟩
  have both : ∀ x ∈ [anchor, anchor], SquareSeen x ([anchor, anchor] ++ gap) := by
    intro x member
    have equal : x = anchor := by simpa using member
    subst x
    exact earlier
  simpa [List.append_assoc] using
    eraseSquaredBlockBeforeSquare ([anchor, anchor] ++ gap) [anchor, anchor] letter both

structure CanonicalBlock where
  letter : Nat
  doubled : Bool
  markerAfter : Bool
deriving Repr, DecidableEq

def renderBlock (anchor : Nat) (block : CanonicalBlock) : List Nat :=
  (if block.doubled then [block.letter, block.letter] else [block.letter]) ++
    (if block.markerAfter then [anchor, anchor] else [])

def renderBlocks (anchor : Nat) (blocks : List CanonicalBlock) : List Nat :=
  blocks.flatMap (renderBlock anchor)

def nextDoubled : List CanonicalBlock → Bool
  | [] => false
  | head :: _ => head.doubled

def pruneHead (head : CanonicalBlock) (tail : List CanonicalBlock) : CanonicalBlock :=
  { head with markerAfter := head.markerAfter && !(head.doubled || nextDoubled tail) }

def pruneSeparators : List CanonicalBlock → List CanonicalBlock
  | [] => []
  | head :: tail => pruneHead head tail :: pruneSeparators tail

theorem nextDoubled_pruneSeparators (blocks : List CanonicalBlock) :
    nextDoubled (pruneSeparators blocks) = nextDoubled blocks := by
  cases blocks <;> rfl

private theorem pruneHead_derives (anchor : Nat) (gap : List Nat)
    (head : CanonicalBlock) (tail : List CanonicalBlock) :
    ListDerives ([anchor, anchor] ++ gap ++ renderBlock anchor head ++ renderBlocks anchor tail)
      ([anchor, anchor] ++ gap ++ renderBlock anchor (pruneHead head tail) ++ renderBlocks anchor tail) := by
  cases head with
  | mk letter doubled marker =>
      cases doubled with
      | false =>
          cases marker with
          | false =>
              simp only [renderBlock, pruneHead, Bool.false_and, Bool.false_eq_true, if_false,
                Bool.false_or, List.append_nil]
              exact S5_107.ListDerives.refl _
          | true =>
              cases tail with
              | nil =>
                  exact S5_107.ListDerives.refl _
              | cons next rest =>
                  cases next with
                  | mk nextLetter nextDouble nextMarker =>
                      cases nextDouble with
                      | false =>
                          exact S5_107.ListDerives.refl _
                      | true =>
                          have step := (eraseMarkerBeforeDoubled anchor nextLetter (gap ++ [letter])).append
                            ((if nextMarker then [anchor, anchor] else []) ++ renderBlocks anchor rest)
                          simpa [renderBlock, renderBlocks, pruneHead, nextDoubled, List.append_assoc] using step
      | true =>
          cases marker with
          | false =>
              exact S5_107.ListDerives.refl _
          | true =>
              have step := (eraseMarkerAfterDoubled anchor letter gap).append (renderBlocks anchor tail)
              simpa [renderBlock, pruneHead, List.append_assoc] using step

/-- The complete separator-pruning derivation under an arbitrary context
following the protected initial anchor square. No distinctness assumption
is needed for this algebraic step. -/
theorem pruneSeparators_derives (anchor : Nat) (gap : List Nat)
    (blocks : List CanonicalBlock) :
    ListDerives ([anchor, anchor] ++ gap ++ renderBlocks anchor blocks)
      ([anchor, anchor] ++ gap ++ renderBlocks anchor (pruneSeparators blocks)) := by
  induction blocks generalizing gap with
  | nil => exact S5_107.ListDerives.refl _
  | cons head tail ih =>
      have first := pruneHead_derives anchor gap head tail
      have second := ih (gap ++ renderBlock anchor (pruneHead head tail))
      have composed := first.trans (by simpa [List.append_assoc] using second)
      simpa [pruneSeparators, renderBlocks, List.append_assoc] using composed

/-- Condition IV, including its terminal boundary: a separator can survive
only after a simple block and, if a next block exists, before a simple block. -/
def AdmissibleMarkers : List CanonicalBlock → Prop
  | [] => True
  | head :: tail =>
      (head.markerAfter = true → head.doubled = false ∧ nextDoubled tail = false) ∧
        AdmissibleMarkers tail

theorem pruneSeparators_admissible (blocks : List CanonicalBlock) :
    AdmissibleMarkers (pruneSeparators blocks) := by
  induction blocks with
  | nil => trivial
  | cons head tail ih =>
      simp only [pruneSeparators, AdmissibleMarkers, nextDoubled_pruneSeparators]
      refine ⟨?_, ih⟩
      cases head with
      | mk letter doubled marker =>
          cases doubled <;> cases marker <;> cases h : nextDoubled tail <;> simp [pruneHead, h]

#print axioms eraseMarkerAfterDoubled
#print axioms eraseMarkerBeforeDoubled
#print axioms pruneSeparators_derives
#print axioms pruneSeparators_admissible

end SemigroupBasis.CoRoots.Order6SporadicSection16

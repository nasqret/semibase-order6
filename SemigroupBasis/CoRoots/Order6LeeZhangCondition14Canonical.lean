import SemigroupBasis.CoRoots.Order6LeeZhangCondition14Invariant

/-!
# Canonical renderer for Lee--Zhang Condition 14

Each connected component is written in the global first-occurrence order.
Every non-anchor letter occurs once or twice according to its source parity;
the anchor block uses the opposite choice because the closing anchor supplies
one additional occurrence.  A simple unary component remains a singleton.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

open SemigroupBasis
open SemigroupBasis.Examples

/-- The parity-selected block for one supported letter.  The component anchor
is treated oppositely because a final anchor is appended by the renderer. -/
def componentParityBlock
    (source : List Nat) (anchor letter : Nat) : List Nat :=
  if letter = anchor then
    if source.count letter % 2 = 0 then [letter] else [letter, letter]
  else if source.count letter % 2 = 0 then [letter, letter] else [letter]

/-- Render one component signature in global first-occurrence order and with
the exact source parity vector. -/
def componentInitialParityRender
    (source initials : List Nat)
    (signature : connectedComponentSignature) : List Nat :=
  let order :=
    initials.filter fun letter =>
      decide (letter ∈ signature.support)
  if signature.support.length = 1 ∧
      signature.repeatedUnary = false then
    order
  else
    match order with
    | [] => []
    | anchor :: rest =>
        componentParityBlock source anchor anchor ++
          rest.flatMap (componentParityBlock source anchor) ++
            [anchor]

/-- The deterministic normal list selected by the exact Condition 14
product-factor signature. -/
def componentInitialParityNormalList (word : Word Nat) : List Nat :=
  let initials := firstOccurrenceSequence word.toList
  (connectedComponentSignaturesWord word).flatMap
    (componentInitialParityRender word.toList initials)

private theorem componentParityBlock_eq_of_parity
    {left right : List Nat}
    (sameParity :
      ∀ letter, left.count letter % 2 = right.count letter % 2)
    (anchor letter : Nat) :
    componentParityBlock left anchor letter =
      componentParityBlock right anchor letter := by
  unfold componentParityBlock
  rw [sameParity letter]

private theorem componentInitialParityRender_eq_of_parity
    {left right : List Nat}
    (sameParity :
      ∀ letter, left.count letter % 2 = right.count letter % 2)
    (initials : List Nat)
    (signature : connectedComponentSignature) :
    componentInitialParityRender left initials signature =
      componentInitialParityRender right initials signature := by
  unfold componentInitialParityRender
  by_cases simple :
      signature.support.length = 1 ∧
        signature.repeatedUnary = false
  · simp [simple]
  · simp only [simple, ↓reduceIte]
    cases orderShape :
        initials.filter
          (fun letter => decide (letter ∈ signature.support)) with
    | nil => simp [orderShape]
    | cons anchor rest =>
        have blockFunction :
            componentParityBlock left anchor =
              componentParityBlock right anchor := by
          funext letter
          exact componentParityBlock_eq_of_parity
            sameParity anchor letter
        simp only [orderShape]
        rw [componentParityBlock_eq_of_parity
          sameParity anchor anchor, blockFunction]

/-- Equality of the exact semantic signature gives literal equality of the
deterministic Condition 14 normal lists. -/
theorem componentInitialParityNormalList_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameComponentInitialParitySignature left right) :
    componentInitialParityNormalList left =
      componentInitialParityNormalList right := by
  unfold componentInitialParityNormalList
  rw [same.componentInitial.components,
    same.componentInitial.initials]
  have renderFunction :
      componentInitialParityRender right.toList
          (firstOccurrenceSequence right.toList) =
        componentInitialParityRender left.toList
          (firstOccurrenceSequence right.toList) := by
    funext signature
    exact (componentInitialParityRender_eq_of_parity
      same.parity
      (firstOccurrenceSequence right.toList)
      signature).symm
  exact congrArg
    (fun render =>
      (connectedComponentSignaturesWord right).flatMap render)
    renderFunction.symm

end SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

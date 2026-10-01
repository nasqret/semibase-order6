import SemigroupBasis.CoRoots.S5_806FinalComponent

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_806

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Exact canonical signature -/

/-- The S5_806 datum consists of every ordered S4_70 component signature
and only the actual final variable of the entire word. -/
structure ConnectedCutSignature where
  components : List connectedComponentSignature
  final : Nat
deriving DecidableEq, Repr

/-- Render the last component with the actual word-final variable as its
endpoint. -/
def renderFinalComponentSignature
    (signature : connectedComponentSignature) (final : Nat) : List Nat :=
  match signature.support with
  | [] => []
  | [letter] =>
      if signature.repeatedUnary then [letter, letter] else [letter]
  | _ :: _ :: _ =>
      final :: normalizedInterior final signature.support ++ [final]

/-- Render all earlier components by their S4_70 signatures and reserve the
actual-final endpoint policy for the last component. -/
def renderConnectedCutComponents :
    List connectedComponentSignature → Nat → List Nat
  | [], _ => []
  | [last], final => renderFinalComponentSignature last final
  | first :: next :: rest, final =>
      connectedComponentRenderSignature first ++
        renderConnectedCutComponents (next :: rest) final

def renderConnectedCutSignature
    (signature : ConnectedCutSignature) : List Nat :=
  renderConnectedCutComponents signature.components signature.final

def connectedCutSignatureOfList
    (letters : List Nat) : ConnectedCutSignature :=
  ⟨connectedComponentSignaturesList letters, componentFinal letters⟩

def connectedCutSignatureOfWord
    (word : Word Nat) : ConnectedCutSignature :=
  connectedCutSignatureOfList word.toList

def SameConnectedCutSignature (left right : Word Nat) : Prop :=
  connectedCutSignatureOfWord left = connectedCutSignatureOfWord right

namespace SameConnectedCutSignature

theorem refl (word : Word Nat) : SameConnectedCutSignature word word := rfl

theorem symm {left right : Word Nat}
    (same : SameConnectedCutSignature left right) :
    SameConnectedCutSignature right left :=
  Eq.symm same

theorem trans {left middle right : Word Nat}
    (first : SameConnectedCutSignature left middle)
    (second : SameConnectedCutSignature middle right) :
    SameConnectedCutSignature left right :=
  Eq.trans first second

end SameConnectedCutSignature

private theorem getLastD_append_nonempty
    (left : List Nat) (leftHead rightHead : Nat)
    (rightTail : List Nat) :
    (left ++ rightHead :: rightTail).getLastD leftHead =
      rightTail.getLastD rightHead := by
  induction left generalizing leftHead with
  | nil =>
      simp only [List.nil_append, List.getLastD_cons]
  | cons letter rest induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction letter

private theorem componentFinal_append_of_right_nonempty
    (left right : List Nat) (rightNonempty : right ≠ []) :
    componentFinal (left ++ right) = componentFinal right := by
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  cases left with
  | nil => rfl
  | cons leftHead leftTail =>
      simp only [List.cons_append, componentFinal]
      exact
        getLastD_append_nonempty
          leftTail leftHead rightHead rightTail

/-- The component-based final renderer is exactly determined by the base
component signature and actual final variable. -/
theorem finalComponentCanonical_eq_renderSignature
    (component : List Nat) :
    finalComponentCanonical component =
      renderFinalComponentSignature
        (connectedComponentSignatureOfList component)
        (componentFinal component) := by
  cases supportShape : connectedComponentSortedSupport component with
  | nil =>
      simp [finalComponentCanonical, renderFinalComponentSignature,
        connectedComponentSignatureOfList, supportShape]
  | cons first remaining =>
      cases remaining with
      | nil =>
          by_cases lengthOne : component.length = 1
          · simp [finalComponentCanonical, renderFinalComponentSignature,
              connectedComponentSignatureOfList, supportShape, lengthOne]
          · simp [finalComponentCanonical, renderFinalComponentSignature,
              connectedComponentSignatureOfList, supportShape, lengthOne]
      | cons second remaining =>
          have interiorEq :
              normalizedInterior (componentFinal component) component =
                normalizedInterior (componentFinal component)
                  (first :: second :: remaining) := by
            apply normalizedInterior_eq_of_mem_iff
            intro tested _
            rw [← supportShape,
              connectedComponentSortedSupport_mem_iff]
          simp [finalComponentCanonical, renderFinalComponentSignature,
            connectedComponentSignatureOfList, supportShape, interiorEq]

private theorem canonicalComponents_eq_renderSignature :
    ∀ (components : List (List Nat)),
      (∀ component, component ∈ components → component ≠ []) →
      canonicalComponents components =
        renderConnectedCutComponents
          (components.map connectedComponentSignatureOfList)
          (componentFinal components.flatten)
  | [], _ => rfl
  | [last], _ => by
      simpa [canonicalComponents, renderConnectedCutComponents] using
        finalComponentCanonical_eq_renderSignature last
  | first :: next :: rest, nonempty => by
      have nextNonempty : next ≠ [] :=
        nonempty next (by simp)
      have tailFlattenNonempty : (next :: rest).flatten ≠ [] := by
        change next ++ rest.flatten ≠ []
        intro flattenedEmpty
        exact nextNonempty (List.append_eq_nil_iff.mp flattenedEmpty).1
      have finalEq :
          componentFinal (first :: next :: rest).flatten =
            componentFinal (next :: rest).flatten := by
        simp only [List.flatten_cons]
        exact componentFinal_append_of_right_nonempty
          first (next :: rest).flatten tailFlattenNonempty
      have recurse :=
        canonicalComponents_eq_renderSignature (next :: rest)
          (fun component componentMember =>
            nonempty component (List.Mem.tail first componentMember))
      have prefixed := congrArg
        (fun suffix =>
          connectedComponentCanonicalComponent first ++ suffix)
        recurse
      rw [finalEq]
      simpa [canonicalComponents, renderConnectedCutComponents,
        connectedComponentCanonicalComponent] using prefixed

/-- The existing normalizer target is precisely the renderer of the exact
S5_806 signature. -/
theorem canonicalRenderList_eq_renderSignature
    (letters : List Nat) :
    canonicalRenderList letters =
      renderConnectedCutSignature
        (connectedCutSignatureOfList letters) := by
  let components := connectedComponentDecomposeList letters
  have rendered :=
    canonicalComponents_eq_renderSignature components
      (connectedComponentDecomposeList_nonempty_components letters)
  have flattenEq := connectedComponentDecomposeList_flatten letters
  simpa [canonicalRenderList, renderConnectedCutSignature,
    connectedCutSignatureOfList, connectedComponentSignaturesList,
    components, flattenEq] using rendered

theorem canonicalRenderList_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    canonicalRenderList letters ≠ [] := by
  cases letters with
  | nil => contradiction
  | cons head tail =>
      exact
        (listDerivesCanonicalRenderComplete
          (head :: tail)).target_ne_nil

def canonicalRender (word : Word Nat) : Word Nat :=
  connectedComponentWordOfNonempty
    (canonicalRenderList word.toList)
    (canonicalRenderList_nonempty (by simp [Word.toList]))

@[simp]
theorem canonicalRender_toList (word : Word Nat) :
    (canonicalRender word).toList = canonicalRenderList word.toList :=
  connectedComponentWordOfNonempty_toList _ _

theorem derivesCanonical (word : Word Nat) :
    Derives basis word (canonicalRender word) := by
  have listed :
      ListDerives word.toList (canonicalRender word).toList := by
    simpa using listDerivesCanonicalRenderComplete word.toList
  cases word with
  | mk sourceHead sourceTail =>
      cases target : canonicalRender ⟨sourceHead, sourceTail⟩ with
      | mk targetHead targetTail =>
          rw [target] at listed
          simpa [S5_107.listWordOfCons] using listed.toWord

theorem canonicalRender_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameConnectedCutSignature left right) :
    canonicalRender left = canonicalRender right := by
  apply Word.toList_injective
  rw [canonicalRender_toList, canonicalRender_toList,
    canonicalRenderList_eq_renderSignature,
    canonicalRenderList_eq_renderSignature]
  change connectedCutSignatureOfWord left =
    connectedCutSignatureOfWord right at same
  simpa [connectedCutSignatureOfWord] using
    congrArg renderConnectedCutSignature same

end SemigroupBasis.CoRoots.S5_806

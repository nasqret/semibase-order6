import SemigroupBasis.CoRoots.S5_804Normalization
import SemigroupBasis.Examples.ConnectedComponentFourComponents

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_804

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Exact final-component signatures -/

/-- Total final-letter selector. Decomposition components are nonempty. -/
def componentFinal : List Nat → Nat
  | [] => 0
  | head :: tail => tail.getLastD head

/-- The S4_70 component datum together with the actual final variable. -/
structure ConnectedCutComponentSignature where
  base : connectedComponentSignature
  final : Nat
deriving DecidableEq, Repr

def connectedCutComponentSignatureOfList
    (component : List Nat) : ConnectedCutComponentSignature :=
  ⟨connectedComponentSignatureOfList component, componentFinal component⟩

/-- Render a component with its actual final variable as the endpoint. -/
def renderConnectedCutComponentSignature
    (signature : ConnectedCutComponentSignature) : List Nat :=
  match signature.base.support with
  | [] => []
  | [letter] =>
      if signature.base.repeatedUnary then [letter, letter] else [letter]
  | _ :: _ :: _ =>
      signature.final ::
        signature.base.support.erase signature.final ++ [signature.final]

def canonicalComponent (component : List Nat) : List Nat :=
  renderConnectedCutComponentSignature
    (connectedCutComponentSignatureOfList component)

def connectedCutSignaturesList
    (letters : List Nat) : List ConnectedCutComponentSignature :=
  (connectedComponentDecomposeList letters).map
    connectedCutComponentSignatureOfList

def connectedCutSignaturesWord
    (word : Word Nat) : List ConnectedCutComponentSignature :=
  connectedCutSignaturesList word.toList

def renderConnectedCutSignatures
    (signatures : List ConnectedCutComponentSignature) : List Nat :=
  signatures.flatMap renderConnectedCutComponentSignature

def canonicalRenderList (letters : List Nat) : List Nat :=
  renderConnectedCutSignatures (connectedCutSignaturesList letters)

/-- Equality of the exact ordered component supports, unary repeat states,
and actual component-final variables. -/
def SameConnectedCutSignature (left right : Word Nat) : Prop :=
  connectedCutSignaturesWord left = connectedCutSignaturesWord right

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

private theorem dropLast_append_final
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [tail.getLastD head] = head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

theorem componentFinal_mem
    (head : Nat) (tail : List Nat) :
    componentFinal (head :: tail) ∈ head :: tail := by
  simpa [componentFinal] using
    (List.getLastD_mem_cons (l := tail) (a := head))

private theorem sortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro letter
    rw [leftNodup.count, rightNodup.count]
    simp only [sameSupport letter]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    leftSorted rightSorted permutation

private theorem interior_eq_nil_of_unary_support
    {component interior : List Nat} {endpoint : Nat}
    (supportShape : connectedComponentSortedSupport component = [endpoint])
    (interiorSupport :
      ∀ tested,
        tested ∈ interior ↔
          tested ∈ component ∧ tested ≠ endpoint) :
    interior = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro tested member
  have sourceMember := (interiorSupport tested).1 member
  have supportMember : tested ∈ [endpoint] := by
    rw [← supportShape, connectedComponentSortedSupport_mem_iff]
    exact sourceMember.1
  have equal : tested = endpoint := by simpa using supportMember
  exact sourceMember.2 equal

private theorem interior_eq_erased_support
    {component interior : List Nat} {endpoint : Nat}
    (endpointMember : endpoint ∈ component)
    (interiorAbsent : endpoint ∉ interior)
    (interiorNodup : interior.Nodup)
    (interiorSorted : interior.Pairwise (· ≤ ·))
    (interiorSupport :
      ∀ tested,
        tested ∈ interior ↔
          tested ∈ component ∧ tested ≠ endpoint) :
    interior =
      (connectedComponentSortedSupport component).erase endpoint := by
  let support := connectedComponentSortedSupport component
  have supportNodup : support.Nodup :=
    connectedComponentSortedSupport_nodup component
  have endpointSupport : endpoint ∈ support :=
    (connectedComponentSortedSupport_mem_iff endpoint component).2
      endpointMember
  apply sortedNodup_eq_of_mem_iff
    interiorSorted
    ((connectedComponentSortedSupport_sorted component).erase endpoint)
    interiorNodup
    (supportNodup.erase endpoint)
  intro tested
  rw [interiorSupport]
  constructor
  · rintro ⟨sourceMember, different⟩
    exact (List.mem_erase_of_ne different).2 <|
      (connectedComponentSortedSupport_mem_iff tested component).2
        sourceMember
  · intro erasedMember
    have supportAndDifferent :=
      supportNodup.mem_erase_iff.mp erasedMember
    exact
      ⟨(connectedComponentSortedSupport_mem_iff tested component).1
          supportAndDifferent.2,
        supportAndDifferent.1⟩

/-! ## Component and whole-word normalization -/

/-- Every nonempty support-connected component derives to its deterministic
actual-final endpoint render. -/
theorem listDerivesCanonicalComponent
    (component : List Nat) (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    ListDerives component (canonicalComponent component) := by
  cases component with
  | nil => contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          have supportShape :
              connectedComponentSortedSupport [head] = [head] := by
            simp [connectedComponentSortedSupport,
              connectedComponentDistinctSupport]
          simpa [canonicalComponent, connectedCutComponentSignatureOfList,
            renderConnectedCutComponentSignature,
            connectedComponentSignatureOfList, componentFinal,
            supportShape] using
              (S5_107.ListDerives.refl (basis := basis) [head])
      | cons next rest =>
          let component := head :: next :: rest
          let endpoint := componentFinal component
          let stem := component.dropLast
          have reconstruction : stem ++ [endpoint] = component := by
            simpa [component, endpoint, stem, componentFinal] using
              dropLast_append_final head (next :: rest)
          have prefixNonempty : stem ≠ [] := by
            intro prefixEmpty
            have lengths := congrArg List.length reconstruction
            rw [prefixEmpty] at lengths
            simp [component] at lengths
          have splitConnected :
              ConnectedComponentSupportConnected
                (stem ++ [endpoint]) := by
            rw [reconstruction]
            exact connected
          obtain
            ⟨interior, derivation, interiorAbsent, interiorNodup,
              interiorSorted, interiorSupport⟩ :=
            existsConnectedComponentNormal
              stem endpoint prefixNonempty splitConnected
          have derivation' :
              ListDerives component
                (endpoint :: interior ++ [endpoint]) := by
            rw [← reconstruction]
            exact derivation
          have interiorSupport' :
              ∀ tested,
                tested ∈ interior ↔
                  tested ∈ component ∧ tested ≠ endpoint := by
            intro tested
            simpa [reconstruction] using interiorSupport tested
          let support := connectedComponentSortedSupport component
          have supportNonempty : support ≠ [] :=
            connectedComponentSortedSupport_nonempty (by simp [component])
          have endpointMember : endpoint ∈ component := by
            simpa [component, endpoint] using
              componentFinal_mem head (next :: rest)
          cases supportShape : support with
          | nil =>
              exact False.elim (supportNonempty supportShape)
          | cons first remaining =>
              cases remaining with
              | nil =>
                  have endpointSupport : endpoint ∈ [first] := by
                    rw [← supportShape]
                    exact
                      (connectedComponentSortedSupport_mem_iff
                        endpoint component).2 endpointMember
                  have endpointEq : endpoint = first := by
                    simpa using endpointSupport
                  subst first
                  have interiorEmpty : interior = [] :=
                    interior_eq_nil_of_unary_support
                      (by simpa [support] using supportShape)
                      interiorSupport'
                  subst interior
                  simpa [canonicalComponent,
                    connectedCutComponentSignatureOfList,
                    renderConnectedCutComponentSignature,
                    connectedComponentSignatureOfList,
                    componentFinal, component, endpoint, support,
                    supportShape] using derivation'
              | cons second remaining =>
                  have interiorEq :
                      interior =
                        (connectedComponentSortedSupport component).erase
                          endpoint :=
                    interior_eq_erased_support endpointMember
                      interiorAbsent interiorNodup interiorSorted
                      interiorSupport'
                  rw [interiorEq] at derivation'
                  simpa [canonicalComponent,
                    connectedCutComponentSignatureOfList,
                    renderConnectedCutComponentSignature,
                    connectedComponentSignatureOfList,
                    componentFinal, component, endpoint, support,
                    supportShape] using derivation'

/-- Normalize every component in an ordered component list. -/
theorem listDerivesCanonicalComponents :
    ∀ (components : List (List Nat)),
      (∀ component, component ∈ components → component ≠ []) →
      (∀ component, component ∈ components →
        ConnectedComponentSupportConnected component) →
      ListDerives
        components.flatten
        (components.flatMap canonicalComponent)
  | [], _, _ => S5_107.ListDerives.empty
  | component :: rest, nonempty, connected => by
      have componentDerivation :=
        listDerivesCanonicalComponent component
          (nonempty component (by simp))
          (connected component (by simp))
      have first := componentDerivation.append rest.flatten
      have recurse :=
        listDerivesCanonicalComponents rest
          (fun current member =>
            nonempty current (List.Mem.tail component member))
          (fun current member =>
            connected current (List.Mem.tail component member))
      have second := recurse.prepend (canonicalComponent component)
      exact first.trans second

theorem canonicalRenderList_eq_flatMap (letters : List Nat) :
    canonicalRenderList letters =
      (connectedComponentDecomposeList letters).flatMap
        canonicalComponent := by
  simp only [canonicalRenderList, renderConnectedCutSignatures,
    connectedCutSignaturesList, List.flatMap_map]
  rfl

/-- Every list derives to its exact S5_804 connected-cut canonical render. -/
theorem listDerivesCanonicalRender (letters : List Nat) :
    ListDerives letters (canonicalRenderList letters) := by
  let components := connectedComponentDecomposeList letters
  have normalized :=
    listDerivesCanonicalComponents components
      (connectedComponentDecomposeList_nonempty_components letters)
      (connectedComponentDecomposeList_supportConnected letters)
  have flattenEq := connectedComponentDecomposeList_flatten letters
  rw [canonicalRenderList_eq_flatMap]
  simpa [components, flattenEq] using normalized

theorem canonicalRenderList_nonempty
    {letters : List Nat} (nonempty : letters ≠ []) :
    canonicalRenderList letters ≠ [] := by
  cases letters with
  | nil => contradiction
  | cons head tail =>
      exact (listDerivesCanonicalRender (head :: tail)).target_ne_nil

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
    simpa using listDerivesCanonicalRender word.toList
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
  rw [canonicalRender_toList, canonicalRender_toList]
  simpa [canonicalRenderList, connectedCutSignaturesWord] using
    congrArg renderConnectedCutSignatures same

end SemigroupBasis.CoRoots.S5_804

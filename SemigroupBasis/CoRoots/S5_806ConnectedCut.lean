import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_806
import SemigroupBasis.Examples.ConnectedComponentFourNormalize

namespace SemigroupBasis.CoRoots.S5_806

open SemigroupBasis
open SemigroupBasis.Examples

abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-! ## Common seven-law envelope calculus -/

/-- Delete a middle occurrence from three separated occurrences of one
nonempty block. -/
theorem derivesThirdOccurrenceDeletion
    (u v z : Word Nat) :
    Derives basis
      ((((u ++ v) ++ u) ++ z) ++ u)
      (((u ++ v) ++ z) ++ u) := by
  have first :=
    derivesClosedInteriorSwap u v (u ++ z)
  have second :=
    (derivesLeftEndpointExpansion u (z ++ v)).symm
  have third :=
    derivesClosedInteriorSwap u z v
  have firstAligned :
      Derives basis
        ((((u ++ v) ++ u) ++ z) ++ u)
        ((((u ++ u) ++ z) ++ v) ++ u) := by
    simpa [Word.append_assoc] using first
  have secondAligned :
      Derives basis
        ((((u ++ u) ++ z) ++ v) ++ u)
        (((u ++ z) ++ v) ++ u) := by
    simpa [Word.append_assoc] using second
  have thirdAligned :
      Derives basis
        (((u ++ z) ++ v) ++ u)
        (((u ++ v) ++ z) ++ u) := by
    simpa [Word.append_assoc] using third
  exact firstAligned.trans (secondAligned.trans thirdAligned)

/-- Swap two possibly empty list blocks inside matching endpoints. -/
theorem listDerivesInteriorSwap
    (endpoint : Nat) (left right : List Nat) :
    ListDerives
      (endpoint :: left ++ right ++ [endpoint])
      (endpoint :: right ++ left ++ [endpoint]) := by
  cases left with
  | nil =>
      simpa [List.append_assoc] using
        (S5_107.ListDerives.refl (basis := basis)
          (endpoint :: right ++ [endpoint]))
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simpa [List.append_assoc] using
            (S5_107.ListDerives.refl (basis := basis)
              (endpoint :: leftHead :: leftTail ++ [endpoint]))
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesClosedInteriorSwap
                  (Word.singleton endpoint)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

/-- Delete the middle of three displayed occurrences, including every
empty/nonempty combination of the two intervening gaps. -/
theorem listDerivesDeleteMiddleCore
    (letter : Nat) (left right : List Nat) :
    ListDerives
      ([letter] ++ left ++ [letter] ++ right ++ [letter])
      ([letter] ++ left ++ right ++ [letter]) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesPowerExpansion (Word.singleton letter)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesLeftEndpointExpansion
                  (Word.singleton letter)
                  (listWordOfCons rightHead rightTail)).symm
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                (derivesRightEndpointExpansion
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)).symm
      | cons rightHead rightTail =>
          exact S5_107.ListDerives.words <| by
            simpa [listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using
                derivesThirdOccurrenceDeletion
                  (Word.singleton letter)
                  (listWordOfCons leftHead leftTail)
                  (listWordOfCons rightHead rightTail)

/-- Delete another endpoint occurrence from an unprocessed suffix. -/
theorem listDerivesEndpointAbsorption
    (endpoint : Nat) (interior before after : List Nat) :
    ListDerives
      (endpoint :: interior ++ endpoint :: before ++ endpoint :: after)
      (endpoint :: (interior ++ before) ++ endpoint :: after) := by
  simpa [List.append_assoc] using
    (listDerivesDeleteMiddleCore endpoint interior before).append after

/-- Lift an interior derivation past one fixed interior letter. -/
theorem listDerivesInteriorCons
    (endpoint letter : Nat) (suffix : List Nat)
    {left right : List Nat}
    (derivation :
      ListDerives
        (endpoint :: left ++ endpoint :: suffix)
        (endpoint :: right ++ endpoint :: suffix)) :
    ListDerives
      (endpoint :: letter :: left ++ endpoint :: suffix)
      (endpoint :: letter :: right ++ endpoint :: suffix) := by
  have first :
      ListDerives
        (endpoint :: letter :: left ++ endpoint :: suffix)
        (endpoint :: letter :: endpoint :: left ++
          endpoint :: suffix) := by
    simpa [List.append_assoc] using
      ((listDerivesDeleteMiddleCore endpoint [letter] left).symm).append
        suffix
  have second :
      ListDerives
        (endpoint :: letter :: endpoint :: left ++ endpoint :: suffix)
        (endpoint :: letter :: endpoint :: right ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      derivation.prepend [endpoint, letter]
  have third :
      ListDerives
        (endpoint :: letter :: endpoint :: right ++ endpoint :: suffix)
        (endpoint :: letter :: right ++ endpoint :: suffix) := by
    simpa [List.append_assoc] using
      (listDerivesDeleteMiddleCore endpoint [letter] right).append suffix
  exact first.trans (second.trans third)

private theorem listDerivesSwapFirstInterior
    (endpoint first second : Nat) (rest suffix : List Nat) :
    ListDerives
      (endpoint :: first :: second :: rest ++ endpoint :: suffix)
      (endpoint :: second :: first :: rest ++ endpoint :: suffix) := by
  cases rest with
  | nil =>
      have core :=
        listDerivesInteriorSwap endpoint [first] [second]
      simpa [List.append_assoc] using core.append suffix
  | cons restHead restTail =>
      let restWord := listWordOfCons restHead restTail
      have firstStep :=
        (derivesThirdOccurrenceDeletion
          (Word.singleton endpoint)
          (Word.singleton first ++ Word.singleton second)
          restWord).symm
      have secondStep :=
        Derives.appendRight
          (derivesClosedInteriorSwap
            (Word.singleton endpoint)
            (Word.singleton first) (Word.singleton second))
          (restWord ++ Word.singleton endpoint)
      have thirdStep :=
        derivesThirdOccurrenceDeletion
          (Word.singleton endpoint)
          (Word.singleton second ++ Word.singleton first)
          restWord
      have firstAligned :
          Derives basis
            (((((Word.singleton endpoint ++ Word.singleton first) ++
              Word.singleton second) ++ restWord) ++
              Word.singleton endpoint))
            ((((((Word.singleton endpoint ++ Word.singleton first) ++
              Word.singleton second) ++ Word.singleton endpoint) ++
              restWord) ++ Word.singleton endpoint)) := by
        simpa [Word.append_assoc] using firstStep
      have secondAligned :
          Derives basis
            ((((((Word.singleton endpoint ++ Word.singleton first) ++
              Word.singleton second) ++ Word.singleton endpoint) ++
              restWord) ++ Word.singleton endpoint))
            ((((((Word.singleton endpoint ++ Word.singleton second) ++
              Word.singleton first) ++ Word.singleton endpoint) ++
              restWord) ++ Word.singleton endpoint)) := by
        simpa [Word.append_assoc] using secondStep
      have thirdAligned :
          Derives basis
            ((((((Word.singleton endpoint ++ Word.singleton second) ++
              Word.singleton first) ++ Word.singleton endpoint) ++
              restWord) ++ Word.singleton endpoint))
            (((((Word.singleton endpoint ++ Word.singleton second) ++
              Word.singleton first) ++ restWord) ++
              Word.singleton endpoint)) := by
        simpa [Word.append_assoc] using thirdStep
      have core :
          ListDerives
            (endpoint :: first :: second :: restHead :: restTail ++
              [endpoint])
            (endpoint :: second :: first :: restHead :: restTail ++
              [endpoint]) :=
        S5_107.ListDerives.words <| by
          simpa [restWord, listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc, List.append_assoc] using
              firstAligned.trans (secondAligned.trans thirdAligned)
      simpa [List.append_assoc] using core.append suffix

/-- Any permutation of an envelope interior is derivable while preserving
an arbitrary suffix after its closing endpoint. -/
theorem listDerivesInteriorPermutation
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    ListDerives
      (endpoint :: left ++ endpoint :: suffix)
      (endpoint :: right ++ endpoint :: suffix) := by
  induction permutation with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons letter _ induction =>
      exact listDerivesInteriorCons endpoint letter suffix induction
  | swap first second rest =>
      exact listDerivesSwapFirstInterior
        endpoint second first rest suffix
  | trans _ _ first second =>
      exact first.trans second

private theorem bind_append (left right : Word Nat)
    (substitution : Nat → Word Nat) :
    (left ++ right).bind substitution =
      left.bind substitution ++ right.bind substitution := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (first second : Nat → Word Nat) :
    (word.bind first).bind second =
      word.bind (fun letter => (first letter).bind second) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- The eighth law contracts one alternating copy before an arbitrary
nonempty right context: `uvuvz = uvuz`. -/
theorem derivesFinalRotationAbsorption
    (u v rightContext : Word Nat) :
    Derives basis
      ((((u ++ v) ++ u) ++ v) ++ rightContext)
      (((u ++ v) ++ u) ++ rightContext) := by
  have rotate :=
    derivesFinalRotation u v (v ++ rightContext)
  have contract :=
    Derives.appendRight
      (derivesRightEndpointExpansion v u).symm rightContext
  have rotateBack :=
    (derivesFinalRotation u v rightContext).symm
  have rotateAligned :
      Derives basis
        ((((u ++ v) ++ u) ++ v) ++ rightContext)
        ((((v ++ u) ++ v) ++ v) ++ rightContext) := by
    simpa [Word.append_assoc] using rotate
  have contractAligned :
      Derives basis
        ((((v ++ u) ++ v) ++ v) ++ rightContext)
        (((v ++ u) ++ v) ++ rightContext) := by
    simpa [Word.append_assoc] using contract
  have rotateBackAligned :
      Derives basis
        (((v ++ u) ++ v) ++ rightContext)
        (((u ++ v) ++ u) ++ rightContext) := by
    simpa [Word.append_assoc] using rotateBack
  exact rotateAligned.trans (contractAligned.trans rotateBackAligned)

/-- The empty-interior endpoint switch before a fixed nonempty context. -/
theorem derivesContextualShortEndpointSwitch
    (oldEndpoint newEndpoint rightContext : Word Nat) :
    Derives basis
      (((((oldEndpoint ++ newEndpoint) ++ newEndpoint) ++
        oldEndpoint) ++ rightContext))
      (((((newEndpoint ++ oldEndpoint) ++ oldEndpoint) ++
        newEndpoint) ++ rightContext)) := by
  have contract :=
    Derives.appendRight
      (derivesMiddleDuplication oldEndpoint newEndpoint).symm
      rightContext
  have rotate :=
    derivesFinalRotation oldEndpoint newEndpoint rightContext
  have duplicate :=
    Derives.appendRight
      (derivesMiddleDuplication newEndpoint oldEndpoint)
      rightContext
  have contractAligned :
      Derives basis
        (((((oldEndpoint ++ newEndpoint) ++ newEndpoint) ++
          oldEndpoint) ++ rightContext))
        (((oldEndpoint ++ newEndpoint) ++ oldEndpoint) ++
          rightContext) := by
    simpa [Word.append_assoc] using contract
  have rotateAligned :
      Derives basis
        (((oldEndpoint ++ newEndpoint) ++ oldEndpoint) ++
          rightContext)
        (((newEndpoint ++ oldEndpoint) ++ newEndpoint) ++
          rightContext) := by
    simpa [Word.append_assoc] using rotate
  have duplicateAligned :
      Derives basis
        (((newEndpoint ++ oldEndpoint) ++ newEndpoint) ++
          rightContext)
        (((((newEndpoint ++ oldEndpoint) ++ oldEndpoint) ++
          newEndpoint) ++ rightContext)) := by
    simpa [Word.append_assoc] using duplicate
  exact contractAligned.trans (rotateAligned.trans duplicateAligned)

/-- Replay every derivation for the complete `S4_70` connected-component
basis while retaining a fixed nonempty right context. The final-rotation law
simulates `xyx = yxy`, while `derivesFinalRotationAbsorption` simulates
`xyx = xyxy` in the reverse direction. -/
theorem liftConnectedComponentDerivation
    {left right : Word Nat}
    (derivation :
      Derives connectedComponentFourBasis left right)
    (rightContext : Word Nat)
    (substitution : Nat → Word Nat) :
    Derives basis
      (left.bind substitution ++ rightContext)
      (right.bind substitution ++ rightContext) := by
  induction derivation generalizing rightContext substitution with
  | fromBasis member =>
      simp only [connectedComponentFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [connectedComponentPowerLaw, connectedComponentXX,
          connectedComponentXXX, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
          Derives.appendRight
            (derivesPowerExpansion (substitution 0)) rightContext
      · simpa [connectedComponentLeftDuplicationLaw,
          connectedComponentXYX, connectedComponentXXYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesLeftEndpointExpansion
              (substitution 0) (substitution 1)) rightContext
      · simpa [connectedComponentMiddleDuplicationLaw,
          connectedComponentXYX, connectedComponentXYYX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesMiddleDuplication
              (substitution 0) (substitution 1)) rightContext
      · simpa [connectedComponentRightDuplicationLaw,
          connectedComponentXYX, connectedComponentXYXX,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.appendRight
            (derivesRightEndpointExpansion
              (substitution 0) (substitution 1)) rightContext
      · simpa [connectedComponentAlternatingLaw,
          connectedComponentXYX, connectedComponentXYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          (derivesFinalRotationAbsorption
            (substitution 0) (substitution 1) rightContext).symm
      · simpa [connectedComponentRotationLaw,
          connectedComponentXYX, connectedComponentYXY,
          Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          derivesFinalRotation
            (substitution 0) (substitution 1) rightContext
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact Derives.symm (induction rightContext substitution)
  | trans _ _ first second =>
      exact Derives.trans
        (first rightContext substitution)
        (second rightContext substitution)
  | prepend stem _ induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.prepend (stem.bind substitution)
          (induction rightContext substitution)
  | appendRight _ suffix induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (suffix.bind substitution ++ rightContext)
          substitution
  | subst _ first induction =>
      simpa [bind_bind] using
        induction rightContext
          (fun letter => (first letter).bind substitution)

/-- Specialized contextual simulation without an additional substitution. -/
theorem liftConnectedComponentDerivationId
    {left right : Word Nat}
    (derivation :
      Derives connectedComponentFourBasis left right)
    (rightContext : Word Nat) :
    Derives basis
      (left ++ rightContext) (right ++ rightContext) := by
  simpa [bind_singleton] using
    liftConnectedComponentDerivation derivation
      rightContext Word.singleton

/-- The fully quantified S4_70 crossing absorption, now valid for S5_806
because a nonempty right context is retained. -/
theorem derivesContextualCrossingAbsorption
    (outer crossing middle before rightContext : Word Nat) :
    Derives basis
      (((((((outer ++ crossing) ++ middle) ++ outer) ++ before) ++
        crossing) ++ rightContext))
      ((((((outer ++ crossing) ++ middle) ++ before) ++ outer) ++
        rightContext)) := by
  simpa [Word.append_assoc] using
    liftConnectedComponentDerivationId
      (connectedComponentDerivesCrossing
        outer crossing middle before)
      rightContext

/-- Change a closed envelope endpoint across an arbitrary nonempty interior
while preserving a nonempty right context. -/
theorem derivesContextualEndpointSwitch
    (oldEndpoint newEndpoint middle rightContext : Word Nat) :
    Derives basis
      ((((((oldEndpoint ++ newEndpoint) ++ newEndpoint) ++ middle) ++
        oldEndpoint) ++ rightContext))
      ((((((newEndpoint ++ oldEndpoint) ++ oldEndpoint) ++ middle) ++
        newEndpoint) ++ rightContext)) := by
  simpa [Word.append_assoc] using
    liftConnectedComponentDerivationId
      (connectedComponentDerivesEndpointSwitch
        oldEndpoint newEndpoint middle)
      rightContext

/-- Lift an S4_70 list derivation before one explicit nonempty list context. -/
theorem liftConnectedComponentListDerivation
    {left right : List Nat}
    (derivation : ConnectedComponentListDerives left right)
    (contextHead : Nat) (contextTail : List Nat) :
    ListDerives
      (left ++ contextHead :: contextTail)
      (right ++ contextHead :: contextTail) := by
  cases derivation with
  | empty =>
      simpa using
        S5_107.ListDerives.refl (basis := basis)
          (contextHead :: contextTail)
  | @words leftHead rightHead leftTail rightTail wordDerivation =>
      exact S5_107.ListDerives.words <| by
        simpa [S5_107.listWordOfCons,
          connectedComponentWordOfCons, Word.append,
          List.append_assoc] using
          liftConnectedComponentDerivationId wordDerivation
            (S5_107.listWordOfCons contextHead contextTail)

/-- Lift an S4_70 list derivation before any proved nonempty list context. -/
theorem liftConnectedComponentListDerivationBefore
    {left right context : List Nat}
    (derivation : ConnectedComponentListDerives left right)
    (contextNonempty : context ≠ []) :
    ListDerives (left ++ context) (right ++ context) := by
  obtain ⟨contextHead, contextTail, rfl⟩ :=
    List.exists_cons_of_ne_nil contextNonempty
  exact liftConnectedComponentListDerivation
    derivation contextHead contextTail

/-- All empty/nonempty filler cases of crossing absorption, with arbitrary
material after the crossing and one fixed nonempty outer context. -/
theorem listDerivesContextualCrossingAbsorption
    (outer crossing : Nat) (middle before after : List Nat)
    (contextHead : Nat) (contextTail : List Nat) :
    ListDerives
      (([outer, crossing] ++ middle ++ [outer] ++ before ++
          [crossing] ++ after) ++ contextHead :: contextTail)
      (([outer, crossing] ++ middle ++ before ++ [outer] ++ after) ++
        contextHead :: contextTail) := by
  have source :=
    (connectedComponentListDerivesCrossing
      outer crossing middle before).append after
  simpa [List.append_assoc] using
    liftConnectedComponentListDerivation source
      contextHead contextTail

/-- Every support-connected component before a nonempty right context
normalizes to the exact least-endpoint S4_70 component render used for an
earlier S5_806 component. -/
theorem listDerivesConnectedComponentCanonicalBefore
    (component : List Nat)
    (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component)
    (contextHead : Nat) (contextTail : List Nat) :
    ListDerives
      (component ++ contextHead :: contextTail)
      (connectedComponentCanonicalComponent component ++
        contextHead :: contextTail) :=
  liftConnectedComponentListDerivation
    (connectedComponentCanonicalComponent_derives
      nonempty connected)
    contextHead contextTail

/-- Quantified connected-cut normalization for an arbitrary prefix. Every
maximal connected component in the prefix receives its least-endpoint
canonical render, while the nonempty right context is retained literally. -/
theorem listDerivesConnectedCanonicalBefore
    (stem : List Nat) (contextHead : Nat)
    (contextTail : List Nat) :
    ListDerives
      (stem ++ contextHead :: contextTail)
      (connectedComponentCanonicalRenderList stem ++
        contextHead :: contextTail) :=
  liftConnectedComponentListDerivation
    (connectedComponentCanonicalRenderList_derives stem)
    contextHead contextTail

/-- Word-level form of quantified connected-cut normalization before a
fixed nonempty word. -/
theorem derivesConnectedCanonicalBefore
    (stem rightContext : Word Nat) :
    Derives basis
      (stem ++ rightContext)
      (connectedComponentCanonicalRender stem ++ rightContext) :=
  liftConnectedComponentDerivationId
    (connectedComponentFour_derivesCanonical stem)
    rightContext

end SemigroupBasis.CoRoots.S5_806

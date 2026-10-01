import SemigroupBasis.CoRoots.S5_415EndpointConnectivity

universe u v

namespace List

/-- Compatibility form of the pointwise relation on two lists. Lean 4.28
removed the former core declaration, while the S5_415 certificates use its
proof-relevant induction principle. -/
inductive Forall₂ {alpha : Type u} {beta : Type v}
    (relation : alpha → beta → Prop) :
    List alpha → List beta → Prop
  | nil : Forall₂ relation [] []
  | cons {left right leftRest rightRest} :
      relation left right →
      Forall₂ relation leftRest rightRest →
      Forall₂ relation (left :: leftRest) (right :: rightRest)

end List

namespace SemigroupBasis.CoRoots.S5_415

open SemigroupBasis

/-! ## Incoming endpoint paths as shared-predecessor pivots -/

/-- Two incoming endpoints are connected by a single pivot when one outgoing
endpoint is constrained to both of them by adjacent pairs in the word. The
equivalence closure records a finite path of such pivots. -/
inductive IncomingPivotConnected (word : Word Nat) : Nat → Nat → Prop
  | refl (letter : Nat) :
      IncomingPivotConnected word letter letter
  | shared {left right predecessor : Nat}
      (leftEdge : (predecessor, left) ∈ word.adjacentPairs)
      (rightEdge : (predecessor, right) ∈ word.adjacentPairs) :
      IncomingPivotConnected word left right
  | symm {left right : Nat} :
      IncomingPivotConnected word left right →
        IncomingPivotConnected word right left
  | trans {left middle right : Nat} :
      IncomingPivotConnected word left middle →
        IncomingPivotConnected word middle right →
          IncomingPivotConnected word left right

/-- One literal shared-predecessor step.  Keeping the predecessor and both
edge witnesses in the step prevents a path replay from silently replacing
endpoint connectivity by a claim about adjacent letters. -/
structure IncomingPivotStep
    (word : Word Nat) (left right : Nat) where
  predecessor : Nat
  leftEdge : (predecessor, left) ∈ word.adjacentPairs
  rightEdge : (predecessor, right) ∈ word.adjacentPairs

def IncomingPivotStep.symm
    {word : Word Nat} {left right : Nat}
    (step : IncomingPivotStep word left right) :
    IncomingPivotStep word right left :=
  ⟨step.predecessor, step.rightEdge, step.leftEdge⟩

/-- Consecutive pivots through the same literal predecessor compress to one
step.  Thus a reduced path never needs to treat the intermediate target as a
new head merely because the same edge witness was reused. -/
def IncomingPivotStep.fuse
    {word : Word Nat} {left middle right : Nat}
    (first : IncomingPivotStep word left middle)
    (second : IncomingPivotStep word middle right)
    (samePredecessor :
      first.predecessor = second.predecessor) :
    IncomingPivotStep word left right := by
  refine ⟨first.predecessor, first.leftEdge, ?_⟩
  simpa [samePredecessor] using second.rightEdge

/-- A linear shared-predecessor path.  Unlike `IncomingPivotConnected`, this
records the exact order in which square-exposure obligations must be met. -/
inductive IncomingPivotPath (word : Word Nat) : Nat → Nat → Type
  | nil (letter : Nat) : IncomingPivotPath word letter letter
  | cons {left middle right : Nat} :
      IncomingPivotStep word left middle →
        IncomingPivotPath word middle right →
          IncomingPivotPath word left right

def IncomingPivotPath.append
    {word : Word Nat} {left middle right : Nat}
    (first : IncomingPivotPath word left middle)
    (second : IncomingPivotPath word middle right) :
    IncomingPivotPath word left right :=
  match first with
  | .nil _ => second
  | .cons step rest =>
      IncomingPivotPath.cons step (rest.append second)

def IncomingPivotPath.symm
    {word : Word Nat} {left right : Nat}
    (path : IncomingPivotPath word left right) :
    IncomingPivotPath word right left :=
  match path with
  | .nil letter => IncomingPivotPath.nil letter
  | .cons step rest =>
      rest.symm.append <|
        IncomingPivotPath.cons step.symm
          (IncomingPivotPath.nil _)

def IncomingPivotPath.fuseFirstTwo
    {word : Word Nat} {left firstMiddle secondMiddle right : Nat}
    (first : IncomingPivotStep word left firstMiddle)
    (second : IncomingPivotStep word firstMiddle secondMiddle)
    (rest : IncomingPivotPath word secondMiddle right)
    (samePredecessor :
      first.predecessor = second.predecessor) :
    IncomingPivotPath word left right :=
  IncomingPivotPath.cons
    (first.fuse second samePredecessor) rest

theorem incomingPivotConnected_of_path
    {word : Word Nat} {left right : Nat}
    (path : IncomingPivotPath word left right) :
    IncomingPivotConnected word left right := by
  induction path with
  | nil letter => exact IncomingPivotConnected.refl letter
  | cons step rest induction =>
      exact IncomingPivotConnected.trans
        (IncomingPivotConnected.shared step.leftEdge step.rightEdge)
        induction

theorem incomingPivotPath_of_connected
    {word : Word Nat} {left right : Nat}
    (connected : IncomingPivotConnected word left right) :
    Nonempty (IncomingPivotPath word left right) := by
  induction connected with
  | refl letter => exact ⟨IncomingPivotPath.nil letter⟩
  | shared leftEdge rightEdge =>
      exact ⟨IncomingPivotPath.cons
        ⟨_, leftEdge, rightEdge⟩
        (IncomingPivotPath.nil _)⟩
  | symm connected induction =>
      rcases induction with ⟨path⟩
      exact ⟨path.symm⟩
  | trans first second firstInduction secondInduction =>
      rcases firstInduction with ⟨firstPath⟩
      rcases secondInduction with ⟨secondPath⟩
      exact ⟨firstPath.append secondPath⟩

theorem incomingPivotPath_iff_connected
    {word : Word Nat} {left right : Nat} :
    Nonempty (IncomingPivotPath word left right) ↔
      IncomingPivotConnected word left right :=
  ⟨fun path => by
      rcases path with ⟨witness⟩
      exact incomingPivotConnected_of_path witness,
    incomingPivotPath_of_connected⟩

/-- Every shared-predecessor path is a path in the full endpoint constraint
graph. -/
theorem endpointConnected_of_incomingPivotConnected
    {word : Word Nat} {left right : Nat}
    (connected : IncomingPivotConnected word left right) :
    BrandtEndpointConnected word
      (BrandtEndpoint.incoming left)
      (BrandtEndpoint.incoming right) := by
  induction connected with
  | refl letter =>
      exact BrandtEndpointConnected.refl _
  | shared leftEdge rightEdge =>
      exact BrandtEndpointConnected.trans
        (BrandtEndpointConnected.symm
          (BrandtEndpointConnected.adjacency leftEdge))
        (BrandtEndpointConnected.adjacency rightEdge)
  | symm connected ih =>
      exact BrandtEndpointConnected.symm ih
  | trans first second firstIH secondIH =>
      exact BrandtEndpointConnected.trans firstIH secondIH

/-- Conversely, a Boolean coloring of shared-predecessor components extends
to a compatible endpoint assignment. Hence every endpoint path between two
incoming vertices has a finite shared-predecessor pivot proof. -/
theorem incomingPivotConnected_of_endpointConnected
    {word : Word Nat} {left right : Nat}
    (connected :
      BrandtEndpointConnected word
        (BrandtEndpoint.incoming left)
        (BrandtEndpoint.incoming right)) :
    IncomingPivotConnected word left right := by
  classical
  apply Decidable.byContradiction
  intro separated
  let incomingColor : Nat → Fin 2 := fun letter =>
    if IncomingPivotConnected word left letter then 0 else 1
  let outgoingColor : Nat → Fin 2 := fun predecessor =>
    if ∃ letter,
        (predecessor, letter) ∈ word.adjacentPairs ∧
          IncomingPivotConnected word left letter then 0 else 1
  let assignment : EndpointAssignment := fun letter =>
    (incomingColor letter, outgoingColor letter)
  have compatible : Compatible assignment word := by
    rw [compatible_iff_adjacent_endpoint_eq]
    intro predecessor target edge
    change outgoingColor predecessor = incomingColor target
    by_cases targetConnected :
        IncomingPivotConnected word left target
    · have witness :
          ∃ letter,
            (predecessor, letter) ∈ word.adjacentPairs ∧
              IncomingPivotConnected word left letter :=
        ⟨target, edge, targetConnected⟩
      simp [outgoingColor, incomingColor, witness, targetConnected]
    · have noWitness :
          ¬∃ letter,
            (predecessor, letter) ∈ word.adjacentPairs ∧
              IncomingPivotConnected word left letter := by
        rintro ⟨letter, letterEdge, letterConnected⟩
        exact targetConnected <|
          IncomingPivotConnected.trans letterConnected
            (IncomingPivotConnected.shared letterEdge edge)
      simp [outgoingColor, incomingColor, noWitness,
        targetConnected]
  have endpointEquality :=
    brandtEndpointValue_eq_of_connected assignment compatible connected
  have leftConnected : IncomingPivotConnected word left left :=
    IncomingPivotConnected.refl left
  have impossible : (0 : Fin 2) = 1 := by
    simpa [assignment, incomingColor, brandtEndpointValue,
      BrandtEndpoint.incoming, leftConnected, separated] using
        endpointEquality
  exact (by decide : (0 : Fin 2) ≠ 1) impossible

theorem incomingPivotConnected_iff_endpointConnected
    {word : Word Nat} {left right : Nat} :
    IncomingPivotConnected word left right ↔
      BrandtEndpointConnected word
        (BrandtEndpoint.incoming left)
        (BrandtEndpoint.incoming right) :=
  ⟨endpointConnected_of_incomingPivotConnected,
    incomingPivotConnected_of_endpointConnected⟩

theorem incomingPivotConnected_iff_of_sameBrandtSignature
    {left right : Word Nat}
    (same : SameBrandtSignature left right)
    (first second : Nat) :
    IncomingPivotConnected left first second ↔
      IncomingPivotConnected right first second := by
  rw [incomingPivotConnected_iff_endpointConnected,
    incomingPivotConnected_iff_endpointConnected]
  exact brandtEndpointConnected_iff_of_sameBrandtSignature same _ _

theorem normalizedIncomingHeadPivotConnected
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    IncomingPivotConnected (normalizeBrandtWord left)
      left.head right.head :=
  incomingPivotConnected_of_endpointConnected
    (normalizedIncomingHeads_connected same)

theorem normalizedIncomingHeadPivotConnected_right
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    IncomingPivotConnected (normalizeBrandtWord right)
      left.head right.head :=
  (incomingPivotConnected_iff_of_sameBrandtSignature
    (normalizedWords_sameBrandtSignature same) left.head right.head).mp
      (normalizedIncomingHeadPivotConnected same)

/-- Choosing the left head as the common literal target is justified by an
explicit pivot path in the normalized right word; this theorem does not yet
claim that the path has been exposed by rewrites. -/
theorem normalizedRightHeadToLeftPivotPath
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    IncomingPivotConnected (normalizeBrandtWord right)
      right.head left.head :=
  IncomingPivotConnected.symm
    (normalizedIncomingHeadPivotConnected_right same)

/-- The same right-head-to-left-head witness in linear form, with every
shared predecessor and both of its literal edge occurrences retained. -/
theorem normalizedRightHeadToLeftLinearPivotPath
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    Nonempty <|
      IncomingPivotPath (normalizeBrandtWord right)
        right.head left.head :=
  incomingPivotPath_of_connected
    (normalizedRightHeadToLeftPivotPath same)

/-! ## Outgoing endpoint paths as shared-successor pivots -/

inductive OutgoingPivotConnected (word : Word Nat) : Nat → Nat → Prop
  | refl (letter : Nat) :
      OutgoingPivotConnected word letter letter
  | shared {left right successor : Nat}
      (leftEdge : (left, successor) ∈ word.adjacentPairs)
      (rightEdge : (right, successor) ∈ word.adjacentPairs) :
      OutgoingPivotConnected word left right
  | symm {left right : Nat} :
      OutgoingPivotConnected word left right →
        OutgoingPivotConnected word right left
  | trans {left middle right : Nat} :
      OutgoingPivotConnected word left middle →
        OutgoingPivotConnected word middle right →
          OutgoingPivotConnected word left right

theorem endpointConnected_of_outgoingPivotConnected
    {word : Word Nat} {left right : Nat}
    (connected : OutgoingPivotConnected word left right) :
    BrandtEndpointConnected word
      (BrandtEndpoint.outgoing left)
      (BrandtEndpoint.outgoing right) := by
  induction connected with
  | refl letter =>
      exact BrandtEndpointConnected.refl _
  | shared leftEdge rightEdge =>
      exact BrandtEndpointConnected.trans
        (BrandtEndpointConnected.adjacency leftEdge)
        (BrandtEndpointConnected.symm
          (BrandtEndpointConnected.adjacency rightEdge))
  | symm connected ih =>
      exact BrandtEndpointConnected.symm ih
  | trans first second firstIH secondIH =>
      exact BrandtEndpointConnected.trans firstIH secondIH

theorem outgoingPivotConnected_of_endpointConnected
    {word : Word Nat} {left right : Nat}
    (connected :
      BrandtEndpointConnected word
        (BrandtEndpoint.outgoing left)
        (BrandtEndpoint.outgoing right)) :
    OutgoingPivotConnected word left right := by
  classical
  apply Decidable.byContradiction
  intro separated
  let outgoingColor : Nat → Fin 2 := fun letter =>
    if OutgoingPivotConnected word left letter then 0 else 1
  let incomingColor : Nat → Fin 2 := fun successor =>
    if ∃ letter,
        (letter, successor) ∈ word.adjacentPairs ∧
          OutgoingPivotConnected word left letter then 0 else 1
  let assignment : EndpointAssignment := fun letter =>
    (incomingColor letter, outgoingColor letter)
  have compatible : Compatible assignment word := by
    rw [compatible_iff_adjacent_endpoint_eq]
    intro source successor edge
    change outgoingColor source = incomingColor successor
    by_cases sourceConnected :
        OutgoingPivotConnected word left source
    · have witness :
          ∃ letter,
            (letter, successor) ∈ word.adjacentPairs ∧
              OutgoingPivotConnected word left letter :=
        ⟨source, edge, sourceConnected⟩
      simp [outgoingColor, incomingColor, witness, sourceConnected]
    · have noWitness :
          ¬∃ letter,
            (letter, successor) ∈ word.adjacentPairs ∧
              OutgoingPivotConnected word left letter := by
        rintro ⟨letter, letterEdge, letterConnected⟩
        exact sourceConnected <|
          OutgoingPivotConnected.trans letterConnected
            (OutgoingPivotConnected.shared letterEdge edge)
      simp [outgoingColor, incomingColor, noWitness,
        sourceConnected]
  have endpointEquality :=
    brandtEndpointValue_eq_of_connected assignment compatible connected
  have leftConnected : OutgoingPivotConnected word left left :=
    OutgoingPivotConnected.refl left
  have impossible : (0 : Fin 2) = 1 := by
    simpa [assignment, outgoingColor, brandtEndpointValue,
      BrandtEndpoint.outgoing, leftConnected, separated] using
        endpointEquality
  exact (by decide : (0 : Fin 2) ≠ 1) impossible

theorem outgoingPivotConnected_iff_endpointConnected
    {word : Word Nat} {left right : Nat} :
    OutgoingPivotConnected word left right ↔
      BrandtEndpointConnected word
        (BrandtEndpoint.outgoing left)
        (BrandtEndpoint.outgoing right) :=
  ⟨endpointConnected_of_outgoingPivotConnected,
    outgoingPivotConnected_of_endpointConnected⟩

theorem outgoingPivotConnected_iff_of_sameBrandtSignature
    {left right : Word Nat}
    (same : SameBrandtSignature left right)
    (first second : Nat) :
    OutgoingPivotConnected left first second ↔
      OutgoingPivotConnected right first second := by
  rw [outgoingPivotConnected_iff_endpointConnected,
    outgoingPivotConnected_iff_endpointConnected]
  exact brandtEndpointConnected_iff_of_sameBrandtSignature same _ _

theorem normalizedOutgoingFinalPivotConnected
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    OutgoingPivotConnected (normalizeBrandtWord left)
      (normalizeBrandtWord left).final
      (normalizeBrandtWord right).final :=
  outgoingPivotConnected_of_endpointConnected <|
    outgoingFinals_connected_of_sameBrandtSignature
      (normalizedWords_sameBrandtSignature same)

theorem normalizedOutgoingFinalPivotConnected_right
    {left right : Word Nat}
    (same : SameBrandtSignature left right) :
    OutgoingPivotConnected (normalizeBrandtWord right)
      (normalizeBrandtWord left).final
      (normalizeBrandtWord right).final :=
  (outgoingPivotConnected_iff_of_sameBrandtSignature
    (normalizedWords_sameBrandtSignature same)
    (normalizeBrandtWord left).final
    (normalizeBrandtWord right).final).mp
      (normalizedOutgoingFinalPivotConnected same)

/-! ## Recursive congruence at a common literal anchor -/

/-- Pointwise derivability for optional excursions; empty excursions only
match empty excursions. -/
inductive OptionalGapDerives :
    Option (Word Nat) → Option (Word Nat) → Prop
  | none : OptionalGapDerives none none
  | some {left right : Word Nat} :
      Derives basis left right →
        OptionalGapDerives (some left) (some right)

theorem OptionalGapDerives.refl :
    ∀ gap : Option (Word Nat), OptionalGapDerives gap gap
  | Option.none => OptionalGapDerives.none
  | Option.some word => OptionalGapDerives.some (Derives.refl word)

theorem OptionalGapDerives.symm
    {left right : Option (Word Nat)}
    (related : OptionalGapDerives left right) :
    OptionalGapDerives right left := by
  cases related with
  | none => exact OptionalGapDerives.none
  | some derivation =>
      exact OptionalGapDerives.some derivation.symm

theorem OptionalGapDerives.trans
    {left middle right : Option (Word Nat)}
    (first : OptionalGapDerives left middle)
    (second : OptionalGapDerives middle right) :
    OptionalGapDerives left right := by
  cases first with
  | none =>
      cases second
      exact OptionalGapDerives.none
  | some firstDerivation =>
      cases second with
      | some secondDerivation =>
          exact OptionalGapDerives.some
            (firstDerivation.trans secondDerivation)

theorem optionalGapDerivesForall₂_refl :
    ∀ gaps : List (Option (Word Nat)),
      List.Forall₂ OptionalGapDerives gaps gaps
  | [] => List.Forall₂.nil
  | gap :: gaps =>
      List.Forall₂.cons (OptionalGapDerives.refl gap)
        (optionalGapDerivesForall₂_refl gaps)

theorem derivesAnchoredGapWalkForall₂
    (anchor : Word Nat)
    {left right : List (Option (Word Nat))}
    (related : List.Forall₂ OptionalGapDerives left right) :
    Derives basis
      (anchoredGapWalk anchor left)
      (anchoredGapWalk anchor right) := by
  induction related with
  | nil => exact Derives.refl _
  | @cons gapLeft gapRight leftRest rightRest
      gapRelated restRelated ih =>
      cases gapRelated with
      | none =>
          simpa [anchoredGapWalk] using Derives.prepend anchor ih
      | @some leftExcursion rightExcursion excursionDerivation =>
          have normalizeExcursion :=
            Derives.appendRight
              (Derives.prepend anchor excursionDerivation)
              (anchoredGapWalk anchor leftRest)
          have normalizeRest :=
            Derives.prepend (anchor ++ rightExcursion) ih
          apply Derives.trans
          · simpa [anchoredGapWalk, Word.append_assoc] using
              normalizeExcursion
          · simpa [anchoredGapWalk, Word.append_assoc] using
              normalizeRest

/-- A possibly empty trailing segment derives pointwise as a nonempty word
when present. -/
inductive TrailingLettersDerives : List Nat → List Nat → Prop
  | nil : TrailingLettersDerives [] []
  | nonempty {leftHead rightHead : Nat}
      {leftTail rightTail : List Nat} :
      Derives basis ⟨leftHead, leftTail⟩ ⟨rightHead, rightTail⟩ →
        TrailingLettersDerives
          (leftHead :: leftTail) (rightHead :: rightTail)

theorem TrailingLettersDerives.refl :
    ∀ letters : List Nat, TrailingLettersDerives letters letters
  | [] => TrailingLettersDerives.nil
  | head :: tail =>
      TrailingLettersDerives.nonempty
        (Derives.refl ⟨head, tail⟩)

theorem TrailingLettersDerives.symm
    {left right : List Nat}
    (related : TrailingLettersDerives left right) :
    TrailingLettersDerives right left := by
  cases related with
  | nil => exact TrailingLettersDerives.nil
  | nonempty derivation =>
      exact TrailingLettersDerives.nonempty derivation.symm

theorem TrailingLettersDerives.trans
    {left middle right : List Nat}
    (first : TrailingLettersDerives left middle)
    (second : TrailingLettersDerives middle right) :
    TrailingLettersDerives left right := by
  cases first with
  | nil =>
      cases second
      exact TrailingLettersDerives.nil
  | nonempty firstDerivation =>
      cases second with
      | nonempty secondDerivation =>
          exact TrailingLettersDerives.nonempty
            (firstDerivation.trans secondDerivation)

/-- Pairwise recursive excursion derivations and a trailing derivation lift
through the same literal anchor. -/
theorem derivesCommonAnchorRebuild
    (anchor : Nat)
    {leftGaps rightGaps : List (Option (Word Nat))}
    {leftTrailing rightTrailing : List Nat}
    (gaps : List.Forall₂ OptionalGapDerives leftGaps rightGaps)
    (trailing :
      TrailingLettersDerives leftTrailing rightTrailing) :
    Derives basis
      (appendTrailingLetters
        (anchoredGapWalk (Word.singleton anchor) leftGaps)
        leftTrailing)
      (appendTrailingLetters
        (anchoredGapWalk (Word.singleton anchor) rightGaps)
        rightTrailing) := by
  have prefixes :=
    derivesAnchoredGapWalkForall₂ (Word.singleton anchor) gaps
  cases leftTrailing with
  | nil =>
      cases rightTrailing with
      | nil =>
          cases trailing
          simpa [appendTrailingLetters] using prefixes
      | cons rightHead rightTail =>
          cases trailing
  | cons leftHead leftTail =>
      cases rightTrailing with
      | nil =>
          cases trailing
      | cons rightHead rightTail =>
          cases trailing with
          | nonempty trailingDerivation =>
              have normalizePrefix :=
                Derives.appendRight prefixes ⟨leftHead, leftTail⟩
              have normalizeTrailing :=
                Derives.prepend
                  (anchoredGapWalk (Word.singleton anchor) rightGaps)
                  trailingDerivation
              apply Derives.trans
              · simpa [appendTrailingLetters] using normalizePrefix
              · simpa [appendTrailingLetters] using normalizeTrailing

/-! ## Leading squares from literal incoming-head edges -/

/-- The nonempty block represented by one optional anchored excursion. -/
def anchoredGapSquareBlock
    (anchor : Word Nat) : Option (Word Nat) → Word Nat
  | none => anchor
  | some excursion => anchor ++ excursion

/-- A represented head excursion can be permuted to the front and duplicated
there.  This is the exact anchored-decomposition form of contextual sandwich
expansion, including the empty-excursion power-law case. -/
theorem derivesExposeAnchoredGapSquare
    (anchor : Word Nat) (gaps : List (Option (Word Nat)))
    (gap : Option (Word Nat)) (member : gap ∈ gaps) :
    Derives basis
      (anchoredGapWalk anchor gaps)
      (((anchoredGapSquareBlock anchor gap ++
          anchoredGapSquareBlock anchor gap) ++
        anchoredGapWalk anchor (gaps.erase gap))) := by
  have expose :
      gaps.Perm (gap :: gaps.erase gap) :=
    List.perm_cons_erase member
  have exposeFront :=
    derivesAnchoredGapWalkPermutation expose anchor
  have duplicateFront :=
    derivesAnchoredGapWalkDuplicateHead
      anchor gap (gaps.erase gap)
  exact exposeFront.trans <| by
    cases gap <;>
      simpa [anchoredGapSquareBlock, anchoredGapWalk,
        Word.append_assoc] using duplicateFront

/-- Lift the preceding square exposure through the exact head decomposition
and its unchanged trailing segment. -/
theorem derivesExposeHeadExcursionSquare
    (word : Word Nat) (gap : Option (Word Nat))
    (member : gap ∈ headExcursions word) :
    Derives basis word
      (appendTrailingLetters
        (((anchoredGapSquareBlock (Word.singleton word.head) gap ++
            anchoredGapSquareBlock (Word.singleton word.head) gap) ++
          anchoredGapWalk (Word.singleton word.head)
            ((headExcursions word).erase gap)))
        (headTrailingSegment word)) := by
  have exposed :=
    derivesAppendTrailingLetters
      (derivesExposeAnchoredGapSquare
        (Word.singleton word.head) (headExcursions word)
        gap member)
      (headTrailingSegment word)
  have fromRebuild :
      Derives basis (headAnchoredRebuild word)
        (appendTrailingLetters
          (((anchoredGapSquareBlock (Word.singleton word.head) gap ++
              anchoredGapSquareBlock (Word.singleton word.head) gap) ++
            anchoredGapWalk (Word.singleton word.head)
              ((headExcursions word).erase gap)))
          (headTrailingSegment word)) := by
    simpa [headAnchoredRebuild] using exposed
  simpa only [headAnchoredRebuild_eq] using fromRebuild

/-- The square exposure consumes only the selected top-level gap.  Every
remaining recursive excursion and the trailing segment retain reflexive
derivation witnesses for a later common-anchor rebuild. -/
theorem exposedHeadSquare_recursiveAlignment
    (word : Word Nat) (gap : Option (Word Nat)) :
    List.Forall₂ OptionalGapDerives
        ((headExcursions word).erase gap)
        ((headExcursions word).erase gap) ∧
      TrailingLettersDerives
        (headTrailingSegment word) (headTrailingSegment word) :=
  ⟨optionalGapDerivesForall₂_refl _,
    TrailingLettersDerives.refl _⟩

/-- The target of a literal adjacent edge occurs in the word tail. -/
theorem adjacentPairTarget_mem_tail
    {word : Word Nat} {source target : Nat}
    (edge : (source, target) ∈ word.adjacentPairs) :
    target ∈ word.tail := by
  cases word with
  | mk head tail =>
      change (source, target) ∈
        Word.adjacentPairsFrom head tail at edge
      change target ∈ tail
      induction tail generalizing head with
      | nil =>
          simp [Word.adjacentPairsFrom] at edge
      | cons next rest induction =>
          simp only [Word.adjacentPairsFrom, List.mem_cons] at edge
          rcases edge with first | later
          · have targetEq : target = next :=
              congrArg Prod.snd first
            simp [targetEq]
          · exact List.mem_cons_of_mem next (induction next later)

private theorem existsAdjacentPairSplitFrom
    (source target : Nat) :
    ∀ (previous : Nat) (letters : List Nat),
      (source, target) ∈
          Word.adjacentPairsFrom previous letters →
        ∃ before after,
          previous :: letters =
            before ++ source :: target :: after
  | previous, [], edge => by
      simp [Word.adjacentPairsFrom] at edge
  | previous, next :: rest, edge => by
      simp only [Word.adjacentPairsFrom, List.mem_cons,
        Prod.mk.injEq] at edge
      rcases edge with first | later
      · rcases first with ⟨sourceEq, targetEq⟩
        subst source
        subst target
        exact ⟨[], rest, rfl⟩
      · rcases existsAdjacentPairSplitFrom
          source target next rest later with
          ⟨before, after, shape⟩
        exact ⟨previous :: before, after, by simp [shape]⟩

/-- Locate an adjacent edge as an exact literal factor of the word. -/
theorem existsToListSplitOfAdjacentPair
    (word : Word Nat) {source target : Nat}
    (edge : (source, target) ∈ word.adjacentPairs) :
    ∃ before after,
      word.toList = before ++ source :: target :: after := by
  cases word with
  | mk head tail =>
      exact existsAdjacentPairSplitFrom
        source target head tail edge

/-- The nonempty word whose letters are a possibly empty prefix followed by
one designated final letter. -/
def wordWithFinalLetter
    (before : List Nat) (final : Nat) : Word Nat :=
  match before with
  | [] => Word.singleton final
  | head :: tail => ⟨head, tail ++ [final]⟩

@[simp]
theorem wordWithFinalLetter_toList
    (before : List Nat) (final : Nat) :
    (wordWithFinalLetter before final).toList = before ++ [final] := by
  cases before <;> simp [wordWithFinalLetter, Word.toList]

@[simp]
theorem wordWithFinalLetter_final
    (before : List Nat) (final : Nat) :
    (wordWithFinalLetter before final).final = final := by
  cases before <;> simp [wordWithFinalLetter, Word.final]

/-- Cubing a product exposes the square of its cyclic conjugate:
`(P Q)² -> (P Q)³ = P (Q P)² Q`.  The two contexts are retained
explicitly; no cancellation or cyclic rotation is being assumed. -/
theorem derivesCyclicConjugateSquareExposure
    (initialSegment suffix : Word Nat) :
    Derives basis
      ((initialSegment ++ suffix) ++ (initialSegment ++ suffix))
      (initialSegment ++
        (((suffix ++ initialSegment) ++ (suffix ++ initialSegment)) ++ suffix)) := by
  simpa [Word.append_assoc] using
    derivesPowerExpansion (initialSegment ++ suffix)

/-- Split a block at a literal edge.  Its cyclic conjugate starts at the
edge target and ends at the edge predecessor, and its square is derivably
exposed under the unavoidable prefix/suffix contexts. -/
theorem existsCyclicSquareExposureOfBlockEdge
    (block : Word Nat) {predecessor target : Nat}
    (edge : (predecessor, target) ∈ block.adjacentPairs) :
    ∃ initialSegment suffix nextBlock : Word Nat,
      block = initialSegment ++ suffix ∧
        initialSegment.final = predecessor ∧
          suffix.head = target ∧
            nextBlock = suffix ++ initialSegment ∧
              nextBlock.head = target ∧
                nextBlock.final = predecessor ∧
                  Derives basis (block ++ block)
                    (initialSegment ++
                      (((nextBlock ++ nextBlock) ++ suffix))) := by
  rcases existsToListSplitOfAdjacentPair block edge with
    ⟨before, after, blockShape⟩
  let initialSegment := wordWithFinalLetter before predecessor
  let suffix : Word Nat := ⟨target, after⟩
  let nextBlock := suffix ++ initialSegment
  have factor : block = initialSegment ++ suffix := by
    apply Word.toList_injective
    rw [blockShape, Word.toList_append]
    simp only [initialSegment, wordWithFinalLetter_toList]
    simp [suffix, Word.toList, List.append_assoc]
  have exposed :
      Derives basis (block ++ block)
        (initialSegment ++ (((nextBlock ++ nextBlock) ++ suffix))) := by
    rw [factor]
    simpa [nextBlock] using
      derivesCyclicConjugateSquareExposure initialSegment suffix
  have initialFinal : initialSegment.final = predecessor := by
    change (wordWithFinalLetter before predecessor).final = predecessor
    exact wordWithFinalLetter_final before predecessor
  exact
    ⟨initialSegment, suffix, nextBlock, factor,
      initialFinal,
      rfl, rfl,
      rfl, by simpa [nextBlock] using initialFinal, exposed⟩

/-- An edge entering the literal head determines a prefix return to that
head.  The interior ends at the stated predecessor, including the empty
interior self-edge case. -/
theorem existsHeadReturnSplitOfIncomingEdge
    (word : Word Nat) {predecessor : Nat}
    (edge : (predecessor, word.head) ∈ word.adjacentPairs) :
    ∃ interior after,
      word.toList =
          [word.head] ++ interior ++ [word.head] ++ after ∧
        interior.getLastD word.head = predecessor := by
  rcases existsToListSplitOfAdjacentPair word edge with
    ⟨before, after, shape⟩
  cases before with
  | nil =>
      have headEq : word.head = predecessor := by
        have heads := congrArg List.head? shape
        simpa [Word.toList] using heads
      refine ⟨[], after, ?_, ?_⟩
      · simpa [headEq] using shape
      · simpa [headEq]
  | cons first rest =>
      have headEq : word.head = first := by
        have heads := congrArg List.head? shape
        simpa [Word.toList] using heads
      subst first
      refine ⟨rest ++ [predecessor], after, ?_, ?_⟩
      · simpa [List.append_assoc] using shape
      · simp

/-- Expose the square associated with the exact incoming-head edge.  The
block starts at the literal head and ends at the shared predecessor, so this
retains the endpoint information needed by the paired pivot edge. -/
theorem existsDerivesExposeSpecificIncomingHeadSquare
    (word : Word Nat) {predecessor : Nat}
    (edge : (predecessor, word.head) ∈ word.adjacentPairs) :
    ∃ block residual : Word Nat,
      block.head = word.head ∧
        block.final = predecessor ∧
          residual.head = word.head ∧
            word = block ++ residual ∧
              Derives basis word ((block ++ block) ++ residual) := by
  rcases existsHeadReturnSplitOfIncomingEdge word edge with
    ⟨interior, after, shape, interiorFinal⟩
  let anchor := Word.singleton word.head
  let block : Word Nat := ⟨word.head, interior⟩
  let residual : Word Nat := ⟨word.head, after⟩
  have blockFinal : block.final = predecessor := by
    simpa [block, Word.final] using interiorFinal
  have coreDerivation :
      Derives basis (block ++ anchor)
        ((block ++ block) ++ anchor) := by
    cases interior with
    | nil =>
        simpa [block, anchor] using derivesPowerExpansion anchor
    | cons first rest =>
        let excursion : Word Nat := ⟨first, rest⟩
        simpa [block, anchor, excursion, Word.append_assoc] using
          derivesSandwichExpansion anchor excursion
  have lifted :=
    derivesAppendTrailingLetters coreDerivation after
  have sourceEq :
      appendTrailingLetters (block ++ anchor) after = word := by
    apply Word.toList_injective
    rw [appendTrailingLetters_toList, shape]
    simp [block, anchor, Word.toList,
      Word.toList_append, List.append_assoc]
  have targetEq :
      appendTrailingLetters ((block ++ block) ++ anchor) after =
        (block ++ block) ++ residual := by
    apply Word.toList_injective
    simp only [appendTrailingLetters_toList, Word.toList_append]
    simp [block, residual, anchor, Word.toList,
      List.append_assoc]
  have wordFactor : word = block ++ residual := by
    apply Word.toList_injective
    rw [shape]
    simp [block, residual, Word.toList,
      Word.toList_append, List.append_assoc]
  refine ⟨block, residual, rfl, blockFinal, rfl, wordFactor, ?_⟩
  rw [← sourceEq, ← targetEq]
  exact lifted

private theorem splitHeadSegments_rest_ne_nil_of_mem
    (anchor : Nat) :
    ∀ (letters : List Nat),
      anchor ∈ letters →
        (splitHeadSegments anchor letters).rest ≠ []
  | [], member => by simp at member
  | letter :: letters, member => by
      by_cases same : letter = anchor
      · subst letter
        simp [splitHeadSegments]
      · have tailMember : anchor ∈ letters := by
          exact (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa [splitHeadSegments, same] using
          splitHeadSegments_rest_ne_nil_of_mem
            anchor letters tailMember

/-- A repeated literal head produces at least one closed optional head
excursion in the exact structural decomposition. -/
theorem headExcursions_ne_nil_of_head_mem_tail
    (word : Word Nat) (member : word.head ∈ word.tail) :
    headExcursions word ≠ [] := by
  have restNonempty :=
    splitHeadSegments_rest_ne_nil_of_mem
      word.head word.tail member
  cases split : splitHeadSegments word.head word.tail with
  | mk first rest =>
      have restNonempty' : rest ≠ [] := by
        simpa [split] using restNonempty
      unfold headExcursions headSegmentLists
      rw [split]
      cases rest with
      | nil => exact False.elim (restNonempty' rfl)
      | cons next tail =>
          simp [HeadSegments.toList, closedHeadGaps]

/-- An edge entering the literal head therefore exposes a concrete leading
square block by the anchored sandwich calculation. -/
theorem existsDerivesExposeHeadSquareOfIncomingEdge
    (word : Word Nat) {predecessor : Nat}
    (edge : (predecessor, word.head) ∈ word.adjacentPairs) :
    ∃ gap : Option (Word Nat),
      gap ∈ headExcursions word ∧
        Derives basis word
          (appendTrailingLetters
            (((anchoredGapSquareBlock
                  (Word.singleton word.head) gap ++
                anchoredGapSquareBlock
                  (Word.singleton word.head) gap) ++
              anchoredGapWalk (Word.singleton word.head)
                ((headExcursions word).erase gap)))
            (headTrailingSegment word)) := by
  have gapsNonempty : headExcursions word ≠ [] :=
    headExcursions_ne_nil_of_head_mem_tail word
      (adjacentPairTarget_mem_tail edge)
  cases gapsShape : headExcursions word with
  | nil => exact False.elim (gapsNonempty gapsShape)
  | cons gap gaps =>
    refine ⟨gap, List.Mem.head gaps, ?_⟩
    have derivation :=
      derivesExposeHeadExcursionSquare word gap (by
        rw [gapsShape]
        exact List.Mem.head gaps)
    simpa only [gapsShape] using derivation

/-- The left edge of one proof-relevant pivot step exposes the first square
needed by a path bank whenever that vertex is the actual literal head.  The
paired right edge is deliberately not claimed to lie in the residual word. -/
theorem IncomingPivotStep.existsDerivesExposeSourceSquare
    {ambient : Word Nat} {left right : Nat}
    (step : IncomingPivotStep ambient left right)
    (sourceHead : ambient.head = left) :
    ∃ gap : Option (Word Nat),
      gap ∈ headExcursions ambient ∧
        Derives basis ambient
          (appendTrailingLetters
            (((anchoredGapSquareBlock
                  (Word.singleton ambient.head) gap ++
                anchoredGapSquareBlock
                  (Word.singleton ambient.head) gap) ++
              anchoredGapWalk (Word.singleton ambient.head)
                ((headExcursions ambient).erase gap)))
            (headTrailingSegment ambient)) := by
  have incomingHead :
      (step.predecessor, ambient.head) ∈ ambient.adjacentPairs := by
    simpa [sourceHead] using step.leftEdge
  exact existsDerivesExposeHeadSquareOfIncomingEdge
    ambient incomingHead

/-- The edge-specific version retains the shared predecessor as the final
letter of the exposed block. -/
theorem IncomingPivotStep.existsDerivesExposeSpecificSourceSquare
    {ambient : Word Nat} {left right : Nat}
    (step : IncomingPivotStep ambient left right)
    (sourceHead : ambient.head = left) :
    ∃ block residual : Word Nat,
      block.head = left ∧
        block.final = step.predecessor ∧
          residual.head = left ∧
            ambient = block ++ residual ∧
              Derives basis ambient ((block ++ block) ++ residual) := by
  have incomingHead :
      (step.predecessor, ambient.head) ∈ ambient.adjacentPairs := by
    simpa [sourceHead] using step.leftEdge
  rcases existsDerivesExposeSpecificIncomingHeadSquare
      ambient incomingHead with
    ⟨block, residual, blockHead, blockFinal, residualHead,
      sourceFactor, exposed⟩
  exact
    ⟨block, residual, blockHead.trans sourceHead,
      blockFinal, residualHead.trans sourceHead,
      sourceFactor, exposed⟩

/-- After factoring at the selected incoming edge, the paired pivot edge is
either internal to the exposed block or remains internal to the residual.
For a nontrivial pivot it cannot be the boundary edge, whose target is the
old literal head. -/
theorem IncomingPivotStep.rightEdge_mem_block_or_residual
    {ambient block residual : Word Nat} {left right : Nat}
    (step : IncomingPivotStep ambient left right)
    (different : left ≠ right)
    (residualHead : residual.head = left)
    (sourceFactor : ambient = block ++ residual) :
    (step.predecessor, right) ∈ block.adjacentPairs ∨
      (step.predecessor, right) ∈ residual.adjacentPairs := by
  have expanded := step.rightEdge
  have expanded' :
      (step.predecessor, right) ∈
        (block ++ residual).adjacentPairs := by
    rw [← sourceFactor]
    exact expanded
  rw [Word.adjacentPairs_append] at expanded'
  rcases List.mem_append.mp expanded' with inBlock | afterBlock
  · exact Or.inl inBlock
  · simp only [List.mem_cons] at afterBlock
    rcases afterBlock with boundary | inResidual
    · have targetEq : right = residual.head :=
        congrArg Prod.snd boundary
      exact False.elim (different (targetEq.trans residualHead).symm)
    · exact Or.inr inResidual

/-! ## Exact contextual rewrites used by path exposure -/

/-- Prepend a possibly empty list to a nonempty word. -/
def retargetPrependLetters : List Nat → Word Nat → Word Nat
  | [], word => word
  | head :: tail, word => ⟨head, tail⟩ ++ word

@[simp]
theorem retargetPrependLetters_toList
    (letters : List Nat) (word : Word Nat) :
    (retargetPrependLetters letters word).toList =
      letters ++ word.toList := by
  cases letters with
  | nil => simp [retargetPrependLetters]
  | cons head tail =>
      simp [retargetPrependLetters, Word.toList_append, Word.toList]

def retargetContext
    (left : List Nat) (core : Word Nat) (right : List Nat) : Word Nat :=
  appendTrailingLetters (retargetPrependLetters left core) right

@[simp]
theorem retargetContext_toList
    (left : List Nat) (core : Word Nat) (right : List Nat) :
    (retargetContext left core right).toList =
      left ++ core.toList ++ right := by
  simp [retargetContext, List.append_assoc]

theorem derivesRetargetPrependLetters
    (letters : List Nat) {source target : Word Nat}
    (derivation : Derives basis source target) :
    Derives basis
      (retargetPrependLetters letters source)
      (retargetPrependLetters letters target) := by
  cases letters with
  | nil => simpa [retargetPrependLetters] using derivation
  | cons head tail =>
      simpa [retargetPrependLetters] using
        Derives.prepend ⟨head, tail⟩ derivation

/-- Every derivation from the three laws lifts through possibly empty raw
left and right contexts. -/
theorem derivesRetargetContext
    (left right : List Nat) {source target : Word Nat}
    (derivation : Derives basis source target) :
    Derives basis
      (retargetContext left source right)
      (retargetContext left target right) :=
  derivesAppendTrailingLetters
    (derivesRetargetPrependLetters left derivation) right

private theorem existsToListPrefixFinal
    (word : Word Nat) :
    ∃ before, word.toList = before ++ [word.final] := by
  cases word with
  | mk head tail =>
      refine ⟨(head :: tail).dropLast, ?_⟩
      have reconstruction :=
        List.dropLast_concat_getLast (l := head :: tail) (by simp)
      rw [List.getLast_eq_getLastD] at reconstruction
      simpa only [Word.toList, Word.final, List.getLastD_cons] using
        reconstruction.symm

private theorem anchoredGapWalk_optionalPair_toList
    (anchor : Nat) (first second : List Nat) :
    (anchoredGapWalk (Word.singleton anchor)
        [optionalWordOfList first, optionalWordOfList second]).toList =
      [anchor] ++ first ++ [anchor] ++ second ++ [anchor] := by
  cases first <;> cases second <;>
    simp [optionalWordOfList, anchoredGapWalk, Word.toList,
      Word.toList_append, List.append_assoc]

/-- Interleaved blocks with a common final letter can be grouped into two
contiguous squares.  Writing the blocks as `U a` and `V a`, this is exactly
the anchored optional-gap swap
`U (a V a U a) V a -> U (a U a V a) V a`; the empty `U` or `V` cases are
handled by the power/sandwich consequences already built into that swap. -/
theorem derivesGroupInterleavedSquaresOfCommonFinal
    (first second : Word Nat)
    (commonFinal : first.final = second.final) :
    Derives basis
      ((first ++ second) ++ (first ++ second))
      ((first ++ first) ++ (second ++ second)) := by
  rcases existsToListPrefixFinal first with
    ⟨firstBefore, firstShape⟩
  rcases existsToListPrefixFinal second with
    ⟨secondBefore, secondShape⟩
  have secondShape' :
      second.toList = secondBefore ++ [first.final] := by
    calc
      second.toList = secondBefore ++ [second.final] := secondShape
      _ = secondBefore ++ [first.final] := by rw [← commonFinal]
  have swapped :=
    derivesRetargetContext firstBefore
      (secondBefore ++ [first.final])
      (derivesAnchoredGapWalkAdjacentSwap
        (Word.singleton first.final)
        (optionalWordOfList secondBefore)
        (optionalWordOfList firstBefore) [])
  have sourceEq :
      retargetContext firstBefore
          (anchoredGapWalk (Word.singleton first.final)
            [optionalWordOfList secondBefore,
              optionalWordOfList firstBefore])
          (secondBefore ++ [first.final]) =
        ((first ++ second) ++ (first ++ second)) := by
    apply Word.toList_injective
    simp [retargetContext_toList,
      anchoredGapWalk_optionalPair_toList,
      firstShape, secondShape', Word.toList_append,
      List.append_assoc]
  have targetEq :
      retargetContext firstBefore
          (anchoredGapWalk (Word.singleton first.final)
            [optionalWordOfList firstBefore,
              optionalWordOfList secondBefore])
          (secondBefore ++ [first.final]) =
        ((first ++ first) ++ (second ++ second)) := by
    apply Word.toList_injective
    simp [retargetContext_toList,
      anchoredGapWalk_optionalPair_toList,
      firstShape, secondShape', Word.toList_append,
      List.append_assoc]
  rw [sourceEq, targetEq] at swapped
  exact swapped

/-- Group the common-final cyclic pieces and then commute their square
blocks.  Unlike a bare cyclic rotation, this changes the literal head only
after both pieces have been exposed as genuine contiguous squares. -/
theorem derivesRotateInterleavedSquaresOfCommonFinal
    (first second : Word Nat)
    (commonFinal : first.final = second.final) :
    Derives basis
      ((first ++ second) ++ (first ++ second))
      ((second ++ second) ++ (first ++ first)) :=
  (derivesGroupInterleavedSquaresOfCommonFinal
    first second commonFinal).trans
      (derivesSquareCommutation first second)

/-- The contexts in `P (Q P)^2 Q` are not discarded.  When `P` and `Q`
end at the same predecessor, power contraction returns to `(P Q)^2`, after
which anchored grouping and square commutation absorb the contexts into the
literal bank `Q^2 P^2`. -/
theorem derivesAbsorbCyclicContextsOfCommonFinal
    (initialSegment suffix : Word Nat)
    (commonFinal : initialSegment.final = suffix.final) :
    Derives basis
      (initialSegment ++
        (((suffix ++ initialSegment) ++ (suffix ++ initialSegment)) ++ suffix))
      ((suffix ++ suffix) ++ (initialSegment ++ initialSegment)) :=
  (derivesCyclicConjugateSquareExposure initialSegment suffix).symm.trans
    (derivesRotateInterleavedSquaresOfCommonFinal
      initialSegment suffix commonFinal)

/-- The preceding cyclic-context absorption is stable under arbitrary raw
left and right contexts. -/
theorem derivesAbsorbCyclicContextsUnderContext
    (left right : List Nat) (initialSegment suffix : Word Nat)
    (commonFinal : initialSegment.final = suffix.final) :
    Derives basis
      (retargetContext left
        (initialSegment ++
          (((suffix ++ initialSegment) ++ (suffix ++ initialSegment)) ++ suffix))
        right)
      (retargetContext left
        ((suffix ++ suffix) ++ (initialSegment ++ initialSegment)) right) :=
  derivesRetargetContext left right
    (derivesAbsorbCyclicContextsOfCommonFinal
      initialSegment suffix commonFinal)

/-- If a pivot edge lies inside a square block ending at its predecessor,
the cyclic split has two common-final pieces.  Their contexts therefore
telescope to a genuine two-square bank whose first block starts at the
pivot target. -/
theorem existsDerivesExposeLeadingSquareBankOfBlockEdge
    (block : Word Nat) {predecessor target : Nat}
    (blockFinal : block.final = predecessor)
    (edge : (predecessor, target) ∈ block.adjacentPairs) :
    ∃ first next : Word Nat,
      block = first ++ next ∧
        first.head = block.head ∧
          first.final = predecessor ∧
            next.head = target ∧
              next.final = predecessor ∧
                Derives basis (block ++ block)
                  ((next ++ next) ++ (first ++ first)) := by
  rcases existsToListSplitOfAdjacentPair block edge with
    ⟨before, after, blockShape⟩
  let first := wordWithFinalLetter before predecessor
  let next : Word Nat := ⟨target, after⟩
  have factor : block = first ++ next := by
    apply Word.toList_injective
    rw [blockShape, Word.toList_append]
    simp only [first, wordWithFinalLetter_toList]
    simp [next, Word.toList, List.append_assoc]
  have firstHead : first.head = block.head := by
    rw [factor]
    rfl
  have firstFinal : first.final = predecessor := by
    simpa [first] using wordWithFinalLetter_final before predecessor
  have nextFinal : next.final = predecessor := by
    calc
      next.final = (first ++ next).final :=
        (Word.final_append first next).symm
      _ = block.final := congrArg Word.final factor.symm
      _ = predecessor := blockFinal
  have commonFinal : first.final = next.final :=
    firstFinal.trans nextFinal.symm
  have exposed :
      Derives basis (block ++ block)
        ((next ++ next) ++ (first ++ first)) := by
    rw [factor]
    exact derivesRotateInterleavedSquaresOfCommonFinal
      first next commonFinal
  exact
    ⟨first, next, factor, firstHead, firstFinal, rfl,
      nextFinal, exposed⟩

/-- Once the paired edge of a pivot is known to be internal to the exposed
source block, the preceding two-square telescope performs the literal head
switch under the untouched residual word. -/
theorem IncomingPivotStep.existsDerivesHeadTargetOfInternalBlockEdge
    {ambient block residual : Word Nat} {left right : Nat}
    (step : IncomingPivotStep ambient left right)
    (blockFinal : block.final = step.predecessor)
    (sourceExposure :
      Derives basis ambient ((block ++ block) ++ residual))
    (internal :
      (step.predecessor, right) ∈ block.adjacentPairs) :
    ∃ targetWord : Word Nat,
      Derives basis ambient targetWord ∧ targetWord.head = right := by
  rcases existsDerivesExposeLeadingSquareBankOfBlockEdge
      block blockFinal internal with
    ⟨first, next, _, _, _, nextHead, _, exposeBank⟩
  let targetWord :=
    ((next ++ next) ++ (first ++ first)) ++ residual
  have liftBank := Derives.appendRight exposeBank residual
  refine ⟨targetWord, sourceExposure.trans liftBank, ?_⟩
  simp [targetWord, nextHead]

/-- One exact telescope step for the residual branch.  If the residual has
itself been rewritten to expose the next square at its literal front, then
contextual lifting makes the two squares adjacent and square commutation
moves the next block to the front.  Neither the old square nor the final
suffix is dropped. -/
theorem derivesResidualSquareTelescope
    {source residual : Word Nat}
    (first next suffix : Word Nat)
    (sourceExposure :
      Derives basis source ((first ++ first) ++ residual))
    (residualExposure :
      Derives basis residual ((next ++ next) ++ suffix)) :
    Derives basis source
      (((next ++ next) ++ (first ++ first)) ++ suffix) := by
  have exposeNext :=
    Derives.prepend (first ++ first) residualExposure
  have commute :=
    Derives.appendRight
      (derivesSquareCommutation first next) suffix
  have exposeNext' :
      Derives basis ((first ++ first) ++ residual)
        (((first ++ first) ++ (next ++ next)) ++ suffix) := by
    simpa [Word.append_assoc] using exposeNext
  have commute' :
      Derives basis
        (((first ++ first) ++ (next ++ next)) ++ suffix)
        (((next ++ next) ++ (first ++ first)) ++ suffix) := by
    simpa [Word.append_assoc] using commute
  exact sourceExposure.trans (exposeNext'.trans commute')

/-- A residual square telescope with the required block head performs the
same literal pivot as the internal-edge branch. -/
theorem existsDerivesHeadTargetOfResidualSquare
    {source residual : Word Nat} {target : Nat}
    (first next suffix : Word Nat)
    (nextHead : next.head = target)
    (sourceExposure :
      Derives basis source ((first ++ first) ++ residual))
    (residualExposure :
      Derives basis residual ((next ++ next) ++ suffix)) :
    ∃ targetWord : Word Nat,
      Derives basis source targetWord ∧ targetWord.head = target := by
  let targetWord :=
    ((next ++ next) ++ (first ++ first)) ++ suffix
  refine
    ⟨targetWord,
      derivesResidualSquareTelescope first next suffix
        sourceExposure residualExposure,
      ?_⟩
  simp [targetWord, nextHead]

/-- Exact one-step case split.  An incoming pivot either retargets the
literal head by a genuine leading square bank, or its paired edge remains in
the residual beginning at the old head.  The second disjunct is the branch
that a path-wide telescope still has to process; it is not silently treated
as an internal occurrence. -/
theorem IncomingPivotStep.existsHeadRetargetOrResidualEdge
    {ambient : Word Nat} {left right : Nat}
    (step : IncomingPivotStep ambient left right)
    (different : left ≠ right)
    (sourceHead : ambient.head = left) :
    ∃ block residual : Word Nat,
      block.head = left ∧
        block.final = step.predecessor ∧
          residual.head = left ∧
            ambient = block ++ residual ∧
              Derives basis ambient ((block ++ block) ++ residual) ∧
                ((∃ targetWord : Word Nat,
                    Derives basis ambient targetWord ∧
                      targetWord.head = right) ∨
                  (step.predecessor, right) ∈
                    residual.adjacentPairs) := by
  rcases step.existsDerivesExposeSpecificSourceSquare sourceHead with
    ⟨block, residual, blockHead, blockFinal, residualHead,
      sourceFactor, sourceExposure⟩
  refine
    ⟨block, residual, blockHead, blockFinal, residualHead,
      sourceFactor, sourceExposure, ?_⟩
  rcases step.rightEdge_mem_block_or_residual
      different residualHead sourceFactor with internal | inResidual
  · exact Or.inl <|
      step.existsDerivesHeadTargetOfInternalBlockEdge
        blockFinal sourceExposure internal
  · exact Or.inr inResidual

/-- Duplicate a nonempty walk enclosed by two copies of the same literal
anchor, at any position in a word. -/
theorem derivesDuplicateEnclosedWalk
    (left right : List Nat) (anchor excursion : Word Nat) :
    Derives basis
      (retargetContext left ((anchor ++ excursion) ++ anchor) right)
      (retargetContext left
        ((((anchor ++ excursion) ++ anchor) ++ excursion) ++ anchor)
        right) :=
  derivesRetargetContext left right
    (derivesSandwichExpansion anchor excursion)

/-- List-level path exposure: split at two literal anchor occurrences and
duplicate the exact nonempty factor between them. -/
theorem existsDuplicateEnclosedFactor
    (current : Word Nat) (before interior after : List Nat)
    (anchor : Nat) (interiorNonempty : interior ≠ [])
    (shape :
      current.toList =
        before ++ [anchor] ++ interior ++ [anchor] ++ after) :
    ∃ expanded : Word Nat,
      Derives basis current expanded ∧
        expanded.toList =
          before ++ [anchor] ++ interior ++ [anchor] ++
            interior ++ [anchor] ++ after := by
  cases interior with
  | nil => exact False.elim (interiorNonempty rfl)
  | cons head tail =>
      let anchorWord := Word.singleton anchor
      let excursion : Word Nat := ⟨head, tail⟩
      let sourceWord :=
        retargetContext before
          ((anchorWord ++ excursion) ++ anchorWord) after
      let targetWord :=
        retargetContext before
          ((((anchorWord ++ excursion) ++ anchorWord) ++ excursion) ++
            anchorWord) after
      have currentEq : current = sourceWord := by
        apply Word.toList_injective
        rw [shape]
        simp only [sourceWord]
        rw [retargetContext_toList]
        simp [anchorWord, excursion,
          Word.toList_append, Word.toList_singleton, Word.toList,
          List.append_assoc]
      have derivation : Derives basis current targetWord := by
        rw [currentEq]
        exact derivesDuplicateEnclosedWalk before after
          anchorWord excursion
      refine ⟨targetWord, derivation, ?_⟩
      simp only [targetWord]
      rw [retargetContext_toList]
      simp [anchorWord, excursion,
        Word.toList_append, Word.toList_singleton, Word.toList,
        List.append_assoc]

/-- If an edge occurs inside a block, the two copies of that block contain
two corresponding target occurrences.  The factor between them is nonempty
and ends at the same predecessor, so contextual sandwich expansion exposes
a nested square whose block starts at the pivot target and ends at that
predecessor. -/
theorem existsDerivesExposeNestedSquareOfSquaredBlockEdge
    (block : Word Nat) {predecessor target : Nat}
    (edge : (predecessor, target) ∈ block.adjacentPairs) :
    ∃ (before : List Nat) (nextBlock residual expanded : Word Nat),
      nextBlock.head = target ∧
        nextBlock.final = predecessor ∧
          Derives basis (block ++ block) expanded ∧
            expanded.toList =
              before ++
                (((nextBlock ++ nextBlock) ++ residual).toList) := by
  rcases existsToListSplitOfAdjacentPair block edge with
    ⟨edgeBefore, edgeAfter, blockShape⟩
  let before := edgeBefore ++ [predecessor]
  let interior := edgeAfter ++ edgeBefore ++ [predecessor]
  let nextBlock : Word Nat := ⟨target, interior⟩
  let residual : Word Nat := ⟨target, edgeAfter⟩
  have interiorNonempty : interior ≠ [] := by
    simp [interior]
  have squaredShape :
      (block ++ block).toList =
        before ++ [target] ++ interior ++ [target] ++ edgeAfter := by
    rw [Word.toList_append, blockShape]
    simp [before, interior, List.append_assoc]
  rcases existsDuplicateEnclosedFactor
      (block ++ block) before interior edgeAfter target
      interiorNonempty squaredShape with
    ⟨expanded, derivation, expandedShape⟩
  have nextFinal : nextBlock.final = predecessor := by
    simp [nextBlock, interior, Word.final]
  refine
    ⟨before, nextBlock, residual, expanded, rfl, nextFinal,
      derivation, ?_⟩
  rw [expandedShape]
  simp [nextBlock, residual, Word.toList,
    Word.toList_append,
    List.append_assoc]

/-- Exchange two nonempty excursions enclosed by a common literal anchor,
inside arbitrary raw contexts. -/
theorem derivesSwapEnclosedWalks
    (left right : List Nat)
    (anchor first second : Word Nat) :
    Derives basis
      (retargetContext left
        ((((anchor ++ first) ++ anchor) ++ second) ++ anchor) right)
      (retargetContext left
        ((((anchor ++ second) ++ anchor) ++ first) ++ anchor) right) :=
  derivesRetargetContext left right
    (derivesGraphSwitch anchor first second)

/-- The empty-excursion boundary of the preceding switch. -/
theorem derivesMoveEmptyEnclosedWalk
    (left right : List Nat) (anchor excursion : Word Nat) :
    Derives basis
      (retargetContext left
        (((anchor ++ anchor) ++ excursion) ++ anchor) right)
      (retargetContext left
        (((anchor ++ excursion) ++ anchor) ++ anchor) right) :=
  derivesRetargetContext left right
    (derivesEmptyExcursionSwap anchor excursion)

/-- Square-block commutation is the only primitive rewrite here that can
change the literal first letter. This contextual form is the local retarget
move used when path exposure has produced two leading square blocks. -/
theorem derivesSwapSquaredWalks
    (left right : List Nat) (first second : Word Nat) :
    Derives basis
      (retargetContext left
        ((first ++ first) ++ (second ++ second)) right)
      (retargetContext left
        ((second ++ second) ++ (first ++ first)) right) :=
  derivesRetargetContext left right
    (derivesSquareCommutation first second)

/-! ## Path-wide square-bank exposure -/

/-- A nonempty bank of squared walks.  The distinguished first block makes
the literal head of the rendered bank explicit. -/
def squaredWalkBank (first : Word Nat) : List (Word Nat) → Word Nat
  | [] => first ++ first
  | next :: rest =>
      (first ++ first) ++ squaredWalkBank next rest

@[simp]
theorem squaredWalkBank_head
    (first : Word Nat) (rest : List (Word Nat)) :
    (squaredWalkBank first rest).head = first.head := by
  cases rest <;> rfl

/-- Move one squared walk across the first block of a nonempty square bank.
The remaining bank is retained as a literal right context. -/
theorem derivesSwapSquaredWalkWithBankHead
    (first second : Word Nat) (rest : List (Word Nat)) :
    Derives basis
      ((first ++ first) ++ squaredWalkBank second rest)
      (squaredWalkBank second (first :: rest)) := by
  cases rest with
  | nil =>
      simpa [squaredWalkBank] using
        derivesSquareCommutation first second
  | cons next tail =>
      simpa [squaredWalkBank, Word.append_assoc] using
        Derives.appendRight
          (derivesSquareCommutation first second)
          (squaredWalkBank next tail)

/-- Blocks indexed by a pivot path.  The constructors prove, rather than
assume, that every block starts at the corresponding path vertex.  No
intermediate vertex is asserted to be the head of the ambient word. -/
inductive SquaredWalkBankAlongPivotPath
    (ambient : Word Nat) :
    {startVertex endVertex : Nat} →
      IncomingPivotPath ambient startVertex endVertex →
      Word Nat → List (Word Nat) → Prop
  | nil {letter : Nat} (block : Word Nat)
      (blockHead : block.head = letter) :
      SquaredWalkBankAlongPivotPath ambient
        (IncomingPivotPath.nil letter) block []
  | cons {left middle right : Nat}
      {step : IncomingPivotStep ambient left middle}
      {path : IncomingPivotPath ambient middle right}
      (block : Word Nat) (blockHead : block.head = left)
      {next : Word Nat} {rest : List (Word Nat)}
      (tailBank :
        SquaredWalkBankAlongPivotPath ambient path next rest) :
      SquaredWalkBankAlongPivotPath ambient
        (IncomingPivotPath.cons step path) block (next :: rest)

/-- Path induction moves only the final square block to the front.  Earlier
vertices remain internal square blocks, so the proof never treats an
intermediate pivot as a valid literal head. -/
theorem derivesSquaredWalkBankToPivotTarget
    {ambient : Word Nat} {startVertex endVertex : Nat}
    {path : IncomingPivotPath ambient startVertex endVertex}
    {first : Word Nat} {rest : List (Word Nat)}
    (along :
      SquaredWalkBankAlongPivotPath ambient path first rest) :
    ∃ targetFirst targetRest,
      targetFirst.head = endVertex ∧
        Derives basis
          (squaredWalkBank first rest)
          (squaredWalkBank targetFirst targetRest) := by
  induction along with
  | nil block blockHead =>
      exact ⟨block, [], blockHead, Derives.refl _⟩
  | cons block blockHead tailBank induction =>
      rcases induction with
        ⟨targetFirst, targetRest, targetHead, moveTail⟩
      have exposeTarget :=
        Derives.prepend (block ++ block) moveTail
      have moveTarget :=
        derivesSwapSquaredWalkWithBankHead
          block targetFirst targetRest
      refine ⟨targetFirst, block :: targetRest, targetHead, ?_⟩
      apply Derives.trans
      · simpa [squaredWalkBank] using exposeTarget
      · exact moveTarget

/-- Conditional replay certificate for an entire pivot path once a contiguous
square bank has genuinely been exposed.  A raw pivot edge only yields the
contextual cyclic shape proved by `existsCyclicSquareExposureOfBlockEdge`;
it does not by itself construct this stronger object. -/
structure IncomingPivotPathSquareBankExposure
    (ambient source : Word Nat) {startVertex endVertex : Nat}
    (path : IncomingPivotPath ambient startVertex endVertex) where
  first : Word Nat
  rest : List (Word Nat)
  suffix : List Nat
  sourceHead : source.head = startVertex
  along : SquaredWalkBankAlongPivotPath ambient path first rest
  expose :
    Derives basis source
      (retargetContext [] (squaredWalkBank first rest) suffix)

/-- A path-wide square-bank exposure produces a genuine derivative whose
literal head is the final pivot.  The head fact comes from the final exposed
block, not from endpoint connectivity. -/
theorem existsDerivesHeadTargetOfPivotPathSquareBankExposure
    {ambient source : Word Nat} {startVertex endVertex : Nat}
    {path : IncomingPivotPath ambient startVertex endVertex}
    (exposure :
      IncomingPivotPathSquareBankExposure ambient source path) :
    ∃ target : Word Nat,
      Derives basis source target ∧ target.head = endVertex := by
  rcases derivesSquaredWalkBankToPivotTarget exposure.along with
    ⟨targetFirst, targetRest, targetHead, moveBank⟩
  let target :=
    retargetContext []
      (squaredWalkBank targetFirst targetRest) exposure.suffix
  have moveUnderSuffix :
      Derives basis
        (retargetContext []
          (squaredWalkBank exposure.first exposure.rest)
          exposure.suffix)
        target := by
    simpa [target] using
      derivesRetargetContext [] exposure.suffix moveBank
  refine ⟨target, exposure.expose.trans moveUnderSuffix, ?_⟩
  simp [target, retargetContext, retargetPrependLetters, targetHead]

/-- Proof-relevant replay of one exposed square bank.  Unlike bare endpoint
connectivity, this records the exact reordered bank, the retained suffix,
and the resulting derivative whose literal head is the path target. -/
structure IncomingPivotPathSquareBankReplay
    {ambient source : Word Nat} {startVertex endVertex : Nat}
    {path : IncomingPivotPath ambient startVertex endVertex}
    (exposure :
      IncomingPivotPathSquareBankExposure ambient source path)
    (target : Word Nat) : Type where
  targetFirst : Word Nat
  targetRest : List (Word Nat)
  targetFirstHead : targetFirst.head = endVertex
  moveBank :
    Derives basis
      (squaredWalkBank exposure.first exposure.rest)
      (squaredWalkBank targetFirst targetRest)
  targetEq :
    target =
      retargetContext []
        (squaredWalkBank targetFirst targetRest) exposure.suffix
  derivation : Derives basis source target
  targetHead : target.head = endVertex

/-- Every genuine square-bank exposure has an exact replay object. -/
theorem existsIncomingPivotPathSquareBankReplay
    {ambient source : Word Nat} {startVertex endVertex : Nat}
    {path : IncomingPivotPath ambient startVertex endVertex}
    (exposure :
      IncomingPivotPathSquareBankExposure ambient source path) :
    ∃ target : Word Nat,
      Nonempty (IncomingPivotPathSquareBankReplay exposure target) := by
  rcases derivesSquaredWalkBankToPivotTarget exposure.along with
    ⟨targetFirst, targetRest, targetFirstHead, moveBank⟩
  let target :=
    retargetContext []
      (squaredWalkBank targetFirst targetRest) exposure.suffix
  have moveUnderSuffix :
      Derives basis
        (retargetContext []
          (squaredWalkBank exposure.first exposure.rest)
          exposure.suffix)
        target := by
    simpa [target] using
      derivesRetargetContext [] exposure.suffix moveBank
  have derivation : Derives basis source target :=
    exposure.expose.trans moveUnderSuffix
  have targetHead : target.head = endVertex := by
    simp [target, retargetContext, retargetPrependLetters,
      targetFirstHead]
  let replay : IncomingPivotPathSquareBankReplay exposure target :=
    { targetFirst := targetFirst
      targetRest := targetRest
      targetFirstHead := targetFirstHead
      moveBank := moveBank
      targetEq := rfl
      derivation := derivation
      targetHead := targetHead }
  exact ⟨target, ⟨replay⟩⟩

/-- This is the exact recursive payload needed after path-wide head
retargeting.  Pairwise optional-gap derivations and the trailing derivation
close the two rebuilt words at the common literal anchor; the right-hand
retarget derivation is then reversed. -/
theorem derivesOfRetargetedCommonAnchor
    {left right retargeted : Word Nat}
    (rightRetarget : Derives basis right retargeted)
    (commonHead : left.head = retargeted.head)
    (gaps :
      List.Forall₂ OptionalGapDerives
        (headExcursions left) (headExcursions retargeted))
    (trailing :
      TrailingLettersDerives
        (headTrailingSegment left)
        (headTrailingSegment retargeted)) :
    Derives basis left right := by
  have alignedRebuild :
      Derives basis
        (headAnchoredRebuild left)
        (headAnchoredRebuild retargeted) := by
    simpa [headAnchoredRebuild, ← commonHead] using
      derivesCommonAnchorRebuild left.head gaps trailing
  have aligned : Derives basis left retargeted := by
    simpa only [headAnchoredRebuild_eq] using alignedRebuild
  exact aligned.trans rightRetarget.symm

/-- A paired decomposition is the complete constructive payload needed for
the final common-anchor argument.  It relates both words: a derivative of the
right word has the literal head of the left word, and its recursive
excursions and trailing segment are derivably aligned with those of the left
word. -/
structure PairedBrandtDecomposition
    (left right : Word Nat) : Type where
  retargeted : Word Nat
  rightRetarget : Derives basis right retargeted
  commonHead : left.head = retargeted.head
  gaps :
    List.Forall₂ OptionalGapDerives
      (headExcursions left) (headExcursions retargeted)
  trailing :
    TrailingLettersDerives
      (headTrailingSegment left)
      (headTrailingSegment retargeted)

theorem PairedBrandtDecomposition.derives
    {left right : Word Nat}
    (paired : PairedBrandtDecomposition left right) :
    Derives basis left right :=
  derivesOfRetargetedCommonAnchor
    paired.rightRetarget paired.commonHead paired.gaps paired.trailing

/-- The stronger active construction route records that the right-hand
retargeting came from an actually exposed square bank, not from an incoming
endpoint path alone. -/
structure PairedSquareBankDecomposition
    (left right : Word Nat) : Type where
  path : IncomingPivotPath right right.head left.head
  exposure :
    IncomingPivotPathSquareBankExposure right right path
  retargeted : Word Nat
  replay :
    IncomingPivotPathSquareBankReplay exposure retargeted
  gaps :
    List.Forall₂ OptionalGapDerives
      (headExcursions left) (headExcursions retargeted)
  trailing :
    TrailingLettersDerives
      (headTrailingSegment left)
      (headTrailingSegment retargeted)

def PairedSquareBankDecomposition.toPaired
    {left right : Word Nat}
    (paired : PairedSquareBankDecomposition left right) :
    PairedBrandtDecomposition left right where
  retargeted := paired.retargeted
  rightRetarget := paired.replay.derivation
  commonHead := paired.replay.targetHead.symm
  gaps := paired.gaps
  trailing := paired.trailing

theorem PairedSquareBankDecomposition.derives
    {left right : Word Nat}
    (paired : PairedSquareBankDecomposition left right) :
    Derives basis left right :=
  paired.toPaired.derives

/-! ## Reversal closure -/

private theorem reversedBasisAxiomDerives
    (identity : Identity Nat)
    (member : identity ∈ reversedBasis basis) :
    Derives basis identity.lhs identity.rhs := by
  change identity ∈ oppositeBasis at member
  rw [oppositeBasis_eq_expected] at member
  simp only [expectedOppositeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Derives.fromBasis (e := powerLaw) (by simp [basis])
  · exact Derives.fromBasis (e := sandwichLaw) (by simp [basis])
  · exact
      (Derives.fromBasis (e := squareCommutationLaw)
        (by simp [basis])).symm

/-- The three-law derivation system is closed under reversing every word.
This supplies the outgoing-endpoint version of each incoming path-exposure
move without introducing a dual assumption. -/
theorem derivesReverse
    {source target : Word Nat}
    (derivation : Derives basis source target) :
    Derives basis source.reverse target.reverse :=
  Derives.transport reversedBasisAxiomDerives derivation.reverse

end SemigroupBasis.CoRoots.S5_415

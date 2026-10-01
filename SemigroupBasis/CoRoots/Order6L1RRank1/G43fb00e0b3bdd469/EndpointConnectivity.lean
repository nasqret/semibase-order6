import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.EndpointSignatureInvariant
import SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469.ContextualFrozen

/-!
# Endpoint-connectivity route for G43

Off-tree source draft.  This file uses only the fresh structural/semantic
route and the indexed frozen-path closure.  In particular it does not import
the retired G43 `Primitives`, `Normalization`, or `Completeness` modules.

The important representation choice is that the role of an occurrence is
computed only from its suffix: an occurrence is `first` when the same letter
occurs later and `last` otherwise.  On a two-limited saturated word these are
exactly the first and last endpoints.  A singleton is consequently tagged
`last`; `SaturatedEndpointState.singletonFinal` is the invariant that keeps
such an unguarded endpoint out of every positive `last`-before-`first`
inversion.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

open SemigroupBasis

inductive EndpointSide where
  | first
  | last
deriving DecidableEq, Repr

structure EndpointTag where
  letter : Nat
  side : EndpointSide
deriving DecidableEq, Repr

namespace EndpointTag

def first (letter : Nat) : EndpointTag :=
  ⟨letter, EndpointSide.first⟩

def last (letter : Nat) : EndpointTag :=
  ⟨letter, EndpointSide.last⟩

end EndpointTag

/-- Chronological occurrence tags.  The test is relative only to the suffix,
which is what makes an adjacent endpoint exchange local. -/
def tagEndpoints : List Nat → List EndpointTag
  | [] => []
  | letter :: suffix =>
      (if letter ∈ suffix then
        EndpointTag.first letter
      else
        EndpointTag.last letter) :: tagEndpoints suffix

@[simp]
theorem tagEndpoints_map_letter :
    ∀ letters : List Nat,
      (tagEndpoints letters).map EndpointTag.letter = letters
  | [] => rfl
  | letter :: suffix => by
      rw [tagEndpoints, List.map_cons,
        tagEndpoints_map_letter suffix]
      by_cases later : letter ∈ suffix <;>
        simp [later, EndpointTag.first, EndpointTag.last]

@[simp]
theorem tagEndpoints_length (letters : List Nat) :
    (tagEndpoints letters).length = letters.length := by
  simpa only [List.length_map] using
    congrArg List.length (tagEndpoints_map_letter letters)

theorem tagEndpoints_drop (letters : List Nat) :
    ∀ offset : Nat,
      (tagEndpoints letters).drop offset =
        tagEndpoints (letters.drop offset)
  | 0 => rfl
  | offset + 1 => by
      cases letters with
      | nil => rfl
      | cons letter suffix =>
          simpa [tagEndpoints] using tagEndpoints_drop suffix offset

/-- The first-role projection of a tag list. -/
def firstProjection : List EndpointTag → List Nat
  | [] => []
  | ⟨letter, .first⟩ :: rest => letter :: firstProjection rest
  | ⟨_, .last⟩ :: rest => firstProjection rest

/-- The last-role projection of a tag list. -/
def lastProjection : List EndpointTag → List Nat
  | [] => []
  | ⟨_, .first⟩ :: rest => lastProjection rest
  | ⟨letter, .last⟩ :: rest => letter :: lastProjection rest

@[simp]
theorem firstProjection_append (left right : List EndpointTag) :
    firstProjection (left ++ right) =
      firstProjection left ++ firstProjection right := by
  induction left with
  | nil => rfl
  | cons tag rest inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side <;>
            simp [firstProjection, inductionHypothesis]

@[simp]
theorem lastProjection_append (left right : List EndpointTag) :
    lastProjection (left ++ right) =
      lastProjection left ++ lastProjection right := by
  induction left with
  | nil => rfl
  | cons tag rest inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side <;>
            simp [lastProjection, inductionHypothesis]

/-- Number of first endpoints in a tag list. -/
def firstEndpointCount : List EndpointTag → Nat
  | [] => 0
  | ⟨_, .first⟩ :: rest => (firstEndpointCount rest).succ
  | ⟨_, .last⟩ :: rest => firstEndpointCount rest

/-- Number of pairs in which a last endpoint occurs before a first endpoint. -/
def lfInversions : List EndpointTag → Nat
  | [] => 0
  | ⟨_, .first⟩ :: rest => lfInversions rest
  | ⟨_, .last⟩ :: rest =>
      firstEndpointCount rest + lfInversions rest

@[simp]
theorem firstEndpointCount_append
    (left right : List EndpointTag) :
    firstEndpointCount (left ++ right) =
      firstEndpointCount left + firstEndpointCount right := by
  induction left with
  | nil => simp [firstEndpointCount]
  | cons tag rest inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side <;>
            simp [firstEndpointCount, inductionHypothesis,
              Nat.succ_add]

/-- Every positive inversion has an adjacent `last, first` boundary. -/
private theorem exists_adjacent_lf_inversion :
    ∀ tags : List EndpointTag,
      0 < lfInversions tags →
        ∃ stem x y suffix,
          tags =
            stem ++ EndpointTag.last x ::
              EndpointTag.first y :: suffix
  | [], positive => by
      simp [lfInversions] at positive
  | ⟨selected, .first⟩ :: rest, positive => by
      have tailPositive : 0 < lfInversions rest := by
        simpa [lfInversions, EndpointTag.first] using positive
      rcases exists_adjacent_lf_inversion rest tailPositive with
        ⟨stem, x, y, suffix, shape⟩
      exact
        ⟨EndpointTag.first selected :: stem, x, y, suffix,
          by simp [shape, EndpointTag.first]⟩
  | ⟨selected, .last⟩ :: rest, positive => by
      cases rest with
      | nil =>
          simp [lfInversions, firstEndpointCount,
            EndpointTag.last] at positive
      | cons next tail =>
          cases next with
          | mk letter side =>
              cases side with
              | first =>
                  exact ⟨[], selected, letter, tail, rfl⟩
              | last =>
                  have tailPositive :
                      0 < lfInversions
                        (EndpointTag.last letter :: tail) := by
                    simp only [lfInversions, firstEndpointCount,
                      EndpointTag.last] at positive ⊢
                    omega
                  rcases exists_adjacent_lf_inversion
                      (EndpointTag.last letter :: tail)
                      tailPositive with
                    ⟨stem, x, y, suffix, shape⟩
                  exact
                    ⟨EndpointTag.last selected :: stem,
                      x, y, suffix, by
                        simpa only [List.cons_append, EndpointTag.last] using
                          congrArg (List.cons (EndpointTag.last selected))
                            shape⟩
termination_by tags => tags.length
decreasing_by
  all_goals simp_all [EndpointTag.first, EndpointTag.last]

/-- An adjacent `last, first` exchange removes exactly one inversion. -/
private theorem lfInversions_adjacent
    (stem suffix : List EndpointTag) (x y : Nat) :
    lfInversions
        (stem ++ EndpointTag.last x ::
          EndpointTag.first y :: suffix) =
      lfInversions
        (stem ++ EndpointTag.first y ::
          EndpointTag.last x :: suffix) + 1 := by
  induction stem with
  | nil =>
      simp [lfInversions, firstEndpointCount,
        EndpointTag.first, EndpointTag.last]
      omega
  | cons tag stem inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side with
          | first =>
              simpa [lfInversions] using inductionHypothesis
          | last =>
              have countEq :
                  firstEndpointCount
                      (stem ++ EndpointTag.last x ::
                        EndpointTag.first y :: suffix) =
                    firstEndpointCount
                      (stem ++ EndpointTag.first y ::
                        EndpointTag.last x :: suffix) := by
                simp [firstEndpointCount_append,
                  firstEndpointCount,
                  EndpointTag.first, EndpointTag.last]
              simp only [List.cons_append, lfInversions]
              rw [countEq, inductionHypothesis]
              omega

private theorem lfInversions_adjacent_lt
    (stem suffix : List EndpointTag) (x y : Nat) :
    lfInversions
        (stem ++ EndpointTag.first y ::
          EndpointTag.last x :: suffix) <
      lfInversions
        (stem ++ EndpointTag.last x ::
          EndpointTag.first y :: suffix) := by
  rw [lfInversions_adjacent]
  omega

/-- State after count trimming and saturation of every letter in the
factor-normal prefix.  The singleton invariant is the exact extra fact
needed to turn a last endpoint occurring before a first endpoint into a
guarded last occurrence. -/
structure SaturatedEndpointState
    (anchor : Word Nat) (letters : List Nat) : Prop where
  twoLimited : ∀ tested, letters.count tested ≤ 2
  prefixSaturated : ∀ tested,
    tested ∈ (jointSignature anchor).factorNormal.dropLast →
      letters.count tested = 2
  singletonFinal : ∀ tested,
    letters.count tested = 1 → letters.getLast? = some tested
  support : ∀ tested,
    tested ∈ letters ↔ tested ∈ anchor.toList
  firstOrder :
    firstProjection (tagEndpoints letters) =
      (jointSignature anchor).factorNormal.dropLast
  lastOrder :
    lastProjection (tagEndpoints letters) =
      (jointSignature anchor).lastOrder
  render :
    (tagEndpoints letters).map EndpointTag.letter = letters

/-! ## Exact endpoint-tag decomposition -/

/-- Dropping a tag prefix exposes the same raw suffix. -/
private theorem adjacent_tag_roles
    {letters : List Nat} {stem suffix : List EndpointTag} {x y : Nat}
    (shape :
      tagEndpoints letters =
        stem ++ EndpointTag.last x :: EndpointTag.first y :: suffix) :
    let before := stem.map EndpointTag.letter
    let after := suffix.map EndpointTag.letter
    letters = before ++ x :: y :: after ∧
      x ∉ y :: after ∧ y ∈ after := by
  let before := stem.map EndpointTag.letter
  let after := suffix.map EndpointTag.letter
  have rawShape : letters = before ++ x :: y :: after := by
    have erased := congrArg (List.map EndpointTag.letter) shape
    simpa [before, after, EndpointTag.first, EndpointTag.last,
      List.map_append] using erased
  have dropped := congrArg (List.drop stem.length) shape
  have tailShape :
      tagEndpoints (x :: y :: after) =
        EndpointTag.last x :: EndpointTag.first y :: suffix := by
    rw [tagEndpoints_drop, rawShape] at dropped
    simpa [before] using dropped
  have xNotLater : x ∉ y :: after := by
    intro later
    have heads := congrArg List.head? tailShape
    simp [tagEndpoints, later, EndpointTag.first,
      EndpointTag.last] at heads
  have yLater : y ∈ after := by
    by_cases later : y ∈ after
    · exact later
    · have seconds :=
        congrArg (fun tags => (tags.drop 1).head?) tailShape
      simp [tagEndpoints, later, EndpointTag.first,
        EndpointTag.last] at seconds
  change
    letters = before ++ x :: y :: after ∧
      x ∉ y :: after ∧ y ∈ after
  exact ⟨rawShape, xNotLater, yLater⟩

/-- Exact six-piece source shape forced by an adjacent tag inversion in a
saturated state.  The earlier `x` and later `y` are precisely the two guards
required by frozen paths 24/9/(1;8⁻¹)/(1;3⁻¹). -/
private theorem saturated_endpoint_tag_decomposition
    (anchor : Word Nat) {letters : List Nat}
    (state : SaturatedEndpointState anchor letters)
    {stem suffix : List EndpointTag} {x y : Nat}
    (tagShape :
      tagEndpoints letters =
        stem ++ EndpointTag.last x :: EndpointTag.first y :: suffix) :
    ∃ before gapLeft gapRight after,
      x ≠ y ∧
      stem.map EndpointTag.letter = before ++ x :: gapLeft ∧
      suffix.map EndpointTag.letter = gapRight ++ y :: after ∧
      letters =
        before ++ [x] ++ gapLeft ++ [x, y] ++
          gapRight ++ [y] ++ after := by
  let rawBefore := stem.map EndpointTag.letter
  let rawAfter := suffix.map EndpointTag.letter
  have roles := adjacent_tag_roles tagShape
  change
    letters = rawBefore ++ x :: y :: rawAfter ∧
      x ∉ y :: rawAfter ∧ y ∈ rawAfter at roles
  rcases roles with ⟨rawShape, xNotLater, yLater⟩
  have different : x ≠ y := by
    intro equal
    subst y
    exact xNotLater (List.Mem.head rawAfter)
  have xPresent : x ∈ letters := by
    rw [rawShape]
    simp
  have xCountPositive : 0 < letters.count x :=
    List.count_pos_iff.mpr xPresent
  have xCountNotOne : letters.count x ≠ 1 := by
    intro countOne
    have finalEq := state.singletonFinal x countOne
    have rawAfterNe : y :: rawAfter ≠ [] := by simp
    have suffixLast :
        (y :: rawAfter).getLast? =
          some ((y :: rawAfter).getLast rawAfterNe) :=
      List.getLast?_eq_some_getLast rawAfterNe
    have suffixShape :
        letters = (rawBefore ++ [x]) ++ (y :: rawAfter) := by
      simpa [List.append_assoc] using rawShape
    rw [suffixShape, List.getLast?_append, suffixLast] at finalEq
    simp only [Option.or] at finalEq
    have selectedEq :
        (y :: rawAfter).getLast rawAfterNe = x :=
      Option.some.inj finalEq
    rw [selectedEq] at suffixLast
    have xInLater : x ∈ y :: rawAfter :=
      List.mem_of_getLast? suffixLast
    exact xNotLater xInLater
  have xCountTwo : letters.count x = 2 := by
    have upper := state.twoLimited x
    omega
  have rawAfterCount : (y :: rawAfter).count x = 0 :=
    List.count_eq_zero.mpr xNotLater
  have rawBeforeCount : rawBefore.count x = 1 := by
    rw [rawShape, List.count_append,
      List.count_cons_self, rawAfterCount] at xCountTwo
    omega
  have xEarlier : x ∈ rawBefore :=
    List.count_pos_iff.mp (by omega)
  obtain ⟨before, gapLeft, beforeShape⟩ :=
    List.mem_iff_append.mp xEarlier
  obtain ⟨gapRight, after, afterShape⟩ :=
    List.mem_iff_append.mp yLater
  refine ⟨before, gapLeft, gapRight, after, different,
    beforeShape, afterShape, ?_⟩
  rw [rawShape, beforeShape, afterShape]
  simp only [List.append_assoc]
  rfl

/-! ## Locality of the endpoint encoder -/

/-- Encode a prefix while regarding `suffix` as its fixed continuation. -/
private def tagPrefix : List Nat → List Nat → List EndpointTag
  | [], _ => []
  | letter :: rest, suffix =>
      (if letter ∈ rest ++ suffix then
        EndpointTag.first letter
      else EndpointTag.last letter) ::
        tagPrefix rest suffix

private theorem tagEndpoints_append
    (leading suffix : List Nat) :
    tagEndpoints (leading ++ suffix) =
      tagPrefix leading suffix ++ tagEndpoints suffix := by
  induction leading with
  | nil => rfl
  | cons letter rest inductionHypothesis =>
      simp only [List.cons_append, tagEndpoints, tagPrefix,
        inductionHypothesis]

private theorem tagPrefix_swap_continuation
    (leading suffix : List Nat) (x y : Nat) :
    tagPrefix leading (x :: y :: suffix) =
      tagPrefix leading (y :: x :: suffix) := by
  induction leading with
  | nil => rfl
  | cons letter rest inductionHypothesis =>
      simp only [tagPrefix]
      have memberEq :
          letter ∈ rest ++ x :: y :: suffix ↔
            letter ∈ rest ++ y :: x :: suffix := by
        simp only [List.mem_append, List.mem_cons,
          or_left_comm, or_comm, or_assoc]
      by_cases member : letter ∈ rest ++ x :: y :: suffix
      · have otherMember := memberEq.mp member
        simp [member, otherMember, inductionHypothesis]
      · have otherAbsent : letter ∉ rest ++ y :: x :: suffix := by
          intro otherMember
          exact member (memberEq.mpr otherMember)
        simp [member, otherAbsent, inductionHypothesis]

/-- Swapping an adjacent tagged `last x, first y` swaps exactly those two
tags and leaves every other tag unchanged. -/
private theorem tagEndpoints_swap_adjacent_lf
    {letters : List Nat} {stem suffix : List EndpointTag} {x y : Nat}
    (shape :
      tagEndpoints letters =
        stem ++ EndpointTag.last x :: EndpointTag.first y :: suffix) :
    tagEndpoints
        (stem.map EndpointTag.letter ++
          y :: x :: suffix.map EndpointTag.letter) =
      stem ++ EndpointTag.first y :: EndpointTag.last x :: suffix := by
  let before := stem.map EndpointTag.letter
  let after := suffix.map EndpointTag.letter
  have roles := adjacent_tag_roles shape
  change
    letters = before ++ x :: y :: after ∧
      x ∉ y :: after ∧ y ∈ after at roles
  rcases roles with ⟨rawShape, xNotLater, yLater⟩
  have different : x ≠ y := by
    intro equal
    subst y
    exact xNotLater (List.Mem.head after)
  have xNotAfter : x ∉ after := by
    intro member
    exact xNotLater (List.Mem.tail y member)
  have sourceTail :
      tagEndpoints (x :: y :: after) =
        EndpointTag.last x :: EndpointTag.first y :: suffix := by
    have dropped := congrArg (List.drop stem.length) shape
    rw [tagEndpoints_drop, rawShape] at dropped
    simpa [before] using dropped
  have afterTags : tagEndpoints after = suffix := by
    have tails :=
      congrArg (fun tags : List EndpointTag => tags.drop 2) sourceTail
    simpa [tagEndpoints] using tails
  have prefixTags :
      tagPrefix before (x :: y :: after) = stem := by
    have expanded :
        tagPrefix before (x :: y :: after) ++
            EndpointTag.last x :: EndpointTag.first y :: suffix =
          stem ++ EndpointTag.last x :: EndpointTag.first y :: suffix := by
      calc
        tagPrefix before (x :: y :: after) ++
            EndpointTag.last x :: EndpointTag.first y :: suffix =
            tagEndpoints (before ++ x :: y :: after) := by
              rw [tagEndpoints_append]
              simp [tagEndpoints, xNotLater, yLater, afterTags,
                EndpointTag.first, EndpointTag.last]
        _ = tagEndpoints letters := by rw [rawShape]
        _ = stem ++ EndpointTag.last x ::
              EndpointTag.first y :: suffix := shape
    exact List.append_cancel_right expanded
  change
    tagEndpoints (before ++ y :: x :: after) =
      stem ++ EndpointTag.first y :: EndpointTag.last x :: suffix
  rw [tagEndpoints_append,
    ← tagPrefix_swap_continuation before after x y,
    prefixTags]
  simp [tagEndpoints, yLater, xNotAfter, Ne.symm different, afterTags,
    EndpointTag.first, EndpointTag.last]

/-! ## The four frozen-path bubble packages -/

private def singletonWord (letter : Nat) : Word Nat :=
  Word.singleton letter

private theorem contextualFrozenBubble
    (before gapLeft gapRight after : List Nat) (x y : Nat) :
    ContextualFrozenRTC
      (before ++ [x] ++ gapLeft ++ [x, y] ++
        gapRight ++ [y] ++ after)
      (before ++ [x] ++ gapLeft ++ [y, x] ++
        gapRight ++ [y] ++ after) := by
  cases gapLeft with
  | nil =>
      cases gapRight with
      | nil =>
          let rule1 : FrozenPathInstantiation :=
            { index := .path00001
              V0 := singletonWord x
              V1 := singletonWord y ++ singletonWord y
              V2 := singletonWord x
              V3 := singletonWord x }
          let witness1 : ContextualFrozenWitness :=
            ⟨rule1, .forward, before, after⟩
          let rule3 : FrozenPathInstantiation :=
            { index := .path00003
              V0 := singletonWord x
              V1 := singletonWord y
              V2 := singletonWord x
              V3 := singletonWord x }
          let witness3 : ContextualFrozenWitness :=
            ⟨rule3, .reverse, before, after⟩
          apply ContextualFrozenRTC.cons
            (middle := before ++ [x, y, y] ++ after)
          · exact ⟨witness1, by
              simp [witness1, rule1, singletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc], by
              simp [witness1, rule1, singletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc]⟩
          · apply ContextualFrozenRTC.cons
              (middle := before ++ [x, y, x, y] ++ after)
            · exact ⟨witness3, by
                simp [witness3, rule3, singletonWord,
                  ContextualFrozenWitness.source,
                  ContextualFrozenWitness.target,
                  ContextualFrozenWitness.coreSource,
                  ContextualFrozenWitness.coreTarget,
                  FrozenPathInstantiation.source,
                  FrozenPathInstantiation.target,
                  Word.singleton, Word.append, Word.toList,
                  List.append_assoc], by
                simp [witness3, rule3, singletonWord,
                  ContextualFrozenWitness.source,
                  ContextualFrozenWitness.target,
                  ContextualFrozenWitness.coreSource,
                  ContextualFrozenWitness.coreTarget,
                  FrozenPathInstantiation.source,
                  FrozenPathInstantiation.target,
                  Word.singleton, Word.append, Word.toList,
                  List.append_assoc]⟩
            · simpa [List.append_assoc] using
                (ContextualFrozenRTC.refl
                  (before ++ [x, y, x, y] ++ after))
      | cons rightHead rightTail =>
          let rightWord : Word Nat := Word.mk rightHead rightTail
          let rule1 : FrozenPathInstantiation :=
            { index := .path00001
              V0 := singletonWord x
              V1 := singletonWord y ++ (rightWord ++ singletonWord y)
              V2 := singletonWord x
              V3 := singletonWord x }
          let witness1 : ContextualFrozenWitness :=
            ⟨rule1, .forward, before, after⟩
          let rule8 : FrozenPathInstantiation :=
            { index := .path00008
              V0 := singletonWord x
              V1 := singletonWord y
              V2 := rightWord
              V3 := singletonWord x }
          let witness8 : ContextualFrozenWitness :=
            ⟨rule8, .reverse, before, after⟩
          apply ContextualFrozenRTC.cons
            (middle := before ++ [x, y] ++
              (rightHead :: rightTail) ++ [y] ++ after)
          · exact ⟨witness1, by
              simp [witness1, rule1, rightWord, singletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc], by
              simp [witness1, rule1, rightWord, singletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc]⟩
          · apply ContextualFrozenRTC.cons
              (middle := before ++ [x, y, x] ++
                (rightHead :: rightTail) ++ [y] ++ after)
            · exact ⟨witness8, by
                simp [witness8, rule8, rightWord, singletonWord,
                  ContextualFrozenWitness.source,
                  ContextualFrozenWitness.target,
                  ContextualFrozenWitness.coreSource,
                  ContextualFrozenWitness.coreTarget,
                  FrozenPathInstantiation.source,
                  FrozenPathInstantiation.target,
                  Word.singleton, Word.append, Word.toList,
                  List.append_assoc], by
                simp [witness8, rule8, rightWord, singletonWord,
                  ContextualFrozenWitness.source,
                  ContextualFrozenWitness.target,
                  ContextualFrozenWitness.coreSource,
                  ContextualFrozenWitness.coreTarget,
                  FrozenPathInstantiation.source,
                  FrozenPathInstantiation.target,
                  Word.singleton, Word.append, Word.toList,
                  List.append_assoc]⟩
            · simpa [List.append_assoc] using
                (ContextualFrozenRTC.refl
                  (before ++ [x, y, x] ++
                    (rightHead :: rightTail) ++ [y] ++ after))
  | cons leftHead leftTail =>
      let leftWord : Word Nat := Word.mk leftHead leftTail
      cases gapRight with
      | nil =>
          let rule9 : FrozenPathInstantiation :=
            { index := .path00009
              V0 := singletonWord x
              V1 := leftWord
              V2 := singletonWord y
              V3 := singletonWord x }
          let witness9 : ContextualFrozenWitness :=
            ⟨rule9, .forward, before, after⟩
          apply ContextualFrozenRTC.cons
            (middle := before ++ [x] ++ (leftHead :: leftTail) ++
              [y, x] ++ [y] ++ after)
          · exact ⟨witness9, by
              simp [witness9, rule9, leftWord, singletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc], by
              simp [witness9, rule9, leftWord, singletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc]⟩
          · simpa [List.append_assoc] using
              (ContextualFrozenRTC.refl
                (before ++ [x] ++ (leftHead :: leftTail) ++
                  [y, x] ++ [y] ++ after))
      | cons rightHead rightTail =>
          let rightWord : Word Nat := Word.mk rightHead rightTail
          let rule24 : FrozenPathInstantiation :=
            { index := .path00024
              V0 := singletonWord x
              V1 := leftWord
              V2 := singletonWord y
              V3 := rightWord }
          let witness24 : ContextualFrozenWitness :=
            ⟨rule24, .forward, before, after⟩
          apply ContextualFrozenRTC.cons
            (middle := before ++ [x] ++ (leftHead :: leftTail) ++
              [y, x] ++ (rightHead :: rightTail) ++ [y] ++ after)
          · exact ⟨witness24, by
              simp [witness24, rule24, leftWord, rightWord,
                singletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc], by
              simp [witness24, rule24, leftWord, rightWord,
                singletonWord,
                ContextualFrozenWitness.source,
                ContextualFrozenWitness.target,
                ContextualFrozenWitness.coreSource,
                ContextualFrozenWitness.coreTarget,
                FrozenPathInstantiation.source,
                FrozenPathInstantiation.target,
                Word.singleton, Word.append, Word.toList,
                List.append_assoc]⟩
          · simpa [List.append_assoc] using
              (ContextualFrozenRTC.refl
                (before ++ [x] ++ (leftHead :: leftTail) ++
                  [y, x] ++ (rightHead :: rightTail) ++ [y] ++ after))

/-! ## One decreasing saturated bubble -/

private theorem count_swap_adjacent
    (before after : List Nat) (x y tested : Nat) :
    (before ++ y :: x :: after).count tested =
      (before ++ x :: y :: after).count tested := by
  simp only [List.count_append, List.count_cons]
  omega

private theorem mem_swap_adjacent
    (before after : List Nat) (x y tested : Nat) :
    tested ∈ before ++ y :: x :: after ↔
      tested ∈ before ++ x :: y :: after := by
  simp only [List.mem_append, List.mem_cons,
    or_left_comm, or_comm, or_assoc]

private theorem getLast?_swap_adjacent_of_after_ne_nil
    (before after : List Nat) (x y : Nat)
    (afterNe : after ≠ []) :
    (before ++ y :: x :: after).getLast? =
      (before ++ x :: y :: after).getLast? := by
  have afterSome :
      after.getLast? = some (after.getLast afterNe) :=
    List.getLast?_eq_some_getLast afterNe
  have appendLast (leading : List Nat) :
      (leading ++ after).getLast? = after.getLast? := by
    rw [List.getLast?_append, afterSome]
    rfl
  calc
    (before ++ y :: x :: after).getLast? =
        ((before ++ [y, x]) ++ after).getLast? := by
          congr 1
          simp [List.append_assoc]
    _ = after.getLast? := appendLast (before ++ [y, x])
    _ = ((before ++ [x, y]) ++ after).getLast? :=
      (appendLast (before ++ [x, y])).symm
    _ = (before ++ x :: y :: after).getLast? := by
      congr 1
      simp [List.append_assoc]

private theorem firstProjection_adjacent_swap
    (stem suffix : List EndpointTag) (x y : Nat) :
    firstProjection
        (stem ++ EndpointTag.first y ::
          EndpointTag.last x :: suffix) =
      firstProjection
        (stem ++ EndpointTag.last x ::
          EndpointTag.first y :: suffix) := by
  simp [firstProjection, EndpointTag.first, EndpointTag.last]

private theorem lastProjection_adjacent_swap
    (stem suffix : List EndpointTag) (x y : Nat) :
    lastProjection
        (stem ++ EndpointTag.first y ::
          EndpointTag.last x :: suffix) =
      lastProjection
        (stem ++ EndpointTag.last x ::
          EndpointTag.first y :: suffix) := by
  simp [lastProjection, EndpointTag.first, EndpointTag.last]

/-- A positive endpoint inversion admits one frozen-path bubble, restores the
saturated state, and strictly decreases the inversion measure. -/
theorem saturated_bubble_progress
    (anchor : Word Nat) {xs : List Nat}
    (state : SaturatedEndpointState anchor xs)
    (positive : 0 < lfInversions (tagEndpoints xs)) :
    ∃ ys,
      ContextualFrozenRTC xs ys ∧
      SaturatedEndpointState anchor ys ∧
      lfInversions (tagEndpoints ys) <
        lfInversions (tagEndpoints xs) := by
  rcases exists_adjacent_lf_inversion
      (tagEndpoints xs) positive with
    ⟨tagStem, x, y, tagSuffix, tagShape⟩
  rcases saturated_endpoint_tag_decomposition
      anchor state tagShape with
    ⟨before, gapLeft, gapRight, after,
      different, rawBeforeShape, rawAfterShape, sourceShape⟩
  let rawBefore := tagStem.map EndpointTag.letter
  let rawAfter := tagSuffix.map EndpointTag.letter
  have roles := adjacent_tag_roles tagShape
  change
    xs = rawBefore ++ x :: y :: rawAfter ∧
      x ∉ y :: rawAfter ∧ y ∈ rawAfter at roles
  rcases roles with ⟨rawShape, xNotLater, yLater⟩
  let ys := rawBefore ++ y :: x :: rawAfter
  have ysTag :
      tagEndpoints ys =
        tagStem ++ EndpointTag.first y ::
          EndpointTag.last x :: tagSuffix := by
    exact tagEndpoints_swap_adjacent_lf tagShape
  have targetShape :
      ys = before ++ [x] ++ gapLeft ++ [y, x] ++
        gapRight ++ [y] ++ after := by
    dsimp [ys, rawBefore, rawAfter]
    rw [rawBeforeShape, rawAfterShape]
    simp only [List.append_assoc]
    rfl
  refine ⟨ys, ?_, ?_, ?_⟩
  · rw [sourceShape, targetShape]
    exact contextualFrozenBubble before gapLeft gapRight after x y
  · refine
      { twoLimited := ?_
        prefixSaturated := ?_
        singletonFinal := ?_
        support := ?_
        firstOrder := ?_
        lastOrder := ?_
        render := tagEndpoints_map_letter ys }
    · intro tested
      rw [count_swap_adjacent rawBefore rawAfter x y tested]
      simpa [rawShape] using state.twoLimited tested
    · intro tested member
      rw [count_swap_adjacent rawBefore rawAfter x y tested]
      simpa [rawShape] using state.prefixSaturated tested member
    · intro tested countOne
      have sourceCountOne : xs.count tested = 1 := by
        rw [rawShape]
        rw [← count_swap_adjacent rawBefore rawAfter x y tested]
        exact countOne
      have sourceFinal := state.singletonFinal tested sourceCountOne
      have rawAfterNe : rawAfter ≠ [] := by
        exact List.ne_nil_of_mem yLater
      have finalsEqual :=
        getLast?_swap_adjacent_of_after_ne_nil
          rawBefore rawAfter x y rawAfterNe
      rw [rawShape] at sourceFinal
      exact finalsEqual.trans sourceFinal
    · intro tested
      rw [mem_swap_adjacent rawBefore rawAfter x y tested]
      simpa [rawShape] using state.support tested
    · rw [ysTag,
        firstProjection_adjacent_swap tagStem tagSuffix x y,
        ← tagShape]
      exact state.firstOrder
    · rw [ysTag,
        lastProjection_adjacent_swap tagStem tagSuffix x y,
        ← tagShape]
      exact state.lastOrder
  · rw [ysTag, tagShape]
    exact lfInversions_adjacent_lt tagStem tagSuffix x y

end SemigroupBasis.CoRoots.Order6L1RRank1.G43fb00e0b3bdd469

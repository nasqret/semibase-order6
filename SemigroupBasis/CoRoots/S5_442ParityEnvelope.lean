import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_441ParityEnvelopeCombinatorics
import SemigroupBasis.CoRoots.S5_442

namespace SemigroupBasis.CoRoots.S5_442

open SemigroupBasis
open SemigroupBasis.Examples

/-- Shared rendering notation for the abstract parity-envelope scanner. -/
abbrev parityEnvelopeRender := S5_441.parityEnvelopeRender

/-- List-level derivability specialized to the `S5_442` 20-law basis. -/
abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

namespace ListDerives

theorem refl (letters : List Nat) :
    S5_107.ListDerives basis letters letters :=
  S5_107.ListDerives.refl (basis := basis) letters

theorem symm {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    S5_107.ListDerives basis right left :=
  S5_107.ListDerives.symm (basis := basis) derivation

theorem trans {left middle right : List Nat}
    (first : S5_107.ListDerives basis left middle)
    (second : S5_107.ListDerives basis middle right) :
    S5_107.ListDerives basis left right :=
  S5_107.ListDerives.trans (basis := basis) first second

theorem prepend (pre : List Nat) {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    S5_107.ListDerives basis (pre ++ left) (pre ++ right) :=
  S5_107.ListDerives.prepend (basis := basis) pre derivation

theorem append {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right)
    (suffix : List Nat) :
    S5_107.ListDerives basis
      (left ++ suffix) (right ++ suffix) :=
  S5_107.ListDerives.append (basis := basis) derivation suffix

theorem context (pre suffix : List Nat) {left right : List Nat}
    (derivation : S5_107.ListDerives basis left right) :
    S5_107.ListDerives basis
      (pre ++ left ++ suffix) (pre ++ right ++ suffix) :=
  S5_107.ListDerives.context
    (basis := basis) pre suffix derivation

theorem ofWord {left right : Word Nat}
    (derivation : Derives basis left right) :
    S5_107.ListDerives basis left.toList right.toList :=
  S5_107.ListDerives.ofWord (basis := basis) derivation

end ListDerives

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- Add or remove two copies of a nonempty block between matching envelope
blocks. -/
theorem derivesEnvelopePower (envelope block : Word Nat) :
    Derives basis
      ((envelope ++ block) ++ envelope)
      ((((envelope ++ block) ++ block) ++ block) ++ envelope) := by
  have base : Derives basis xyx xyyyx :=
    Derives.fromBasis (e := xyxXYYYXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords envelope block block)
  simpa [xyxXYYYXLaw, xyx, xyyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Add or remove two copies of the left envelope block. -/
theorem derivesLeftEnvelopePower (envelope middle : Word Nat) :
    Derives basis
      ((envelope ++ middle) ++ envelope)
      ((((envelope ++ envelope) ++ envelope) ++ middle) ++ envelope) := by
  have base : Derives basis xyx xxxyx :=
    Derives.fromBasis (e := xyxXXXYXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords envelope middle middle)
  simpa [xyxXXXYXLaw, xyx, xxxyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Add or remove two copies of the right envelope block. -/
theorem derivesRightEnvelopePower (envelope middle : Word Nat) :
    Derives basis
      ((envelope ++ middle) ++ envelope)
      ((((envelope ++ middle) ++ envelope) ++ envelope) ++ envelope) := by
  have base : Derives basis xyx xyxxx :=
    Derives.fromBasis (e := xyxXYXXXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords envelope middle middle)
  simpa [xyxXYXXXLaw, xyx, xyxxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap adjacent nonempty blocks inside matching envelope blocks. -/
theorem derivesInteriorSwap
    (envelope left right : Word Nat) :
    Derives basis
      (((envelope ++ left) ++ right) ++ envelope)
      (((envelope ++ right) ++ left) ++ envelope) := by
  have base : Derives basis xyzx xzyx :=
    Derives.fromBasis (e := xyzxXZYXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords envelope left right)
  simpa [xyzxXZYXLaw, xyzx, xzyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Expand two adjacent copies of a nonempty block to four copies. -/
theorem derivesBlockSquarePower (block : Word Nat) :
    Derives basis
      (block ++ block)
      (((block ++ block) ++ block) ++ block) := by
  have base : Derives basis xx xxxx :=
    Derives.fromBasis (e := powerLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords block block block)
  simpa [powerLaw, xx, xxxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Move one repeated endpoint copy from the left side to the right. -/
theorem derivesEndpointTransfer (endpoint middle : Word Nat) :
    Derives basis
      (((endpoint ++ endpoint) ++ middle) ++ endpoint)
      (((endpoint ++ middle) ++ endpoint) ++ endpoint) := by
  have base : Derives basis xxyx xyxx :=
    Derives.fromBasis (e := xxyxXYXXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base
      (instantiateThreeWords endpoint middle middle)
  simpa [xxyxXYXXLaw, xxyx, xyxx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The component-preserving attachment rewrite
`x y x z y = x y y z x`. -/
theorem derivesAttachmentXYYZX (x y z : Word Nat) :
    Derives basis
      ((((x ++ y) ++ x) ++ z) ++ y)
      ((((x ++ y) ++ y) ++ z) ++ x) := by
  have base : Derives basis xyxzy xyyzx :=
    Derives.fromBasis (e := xyxzyXYYZXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords x y z)
  simpa [xyxzyXYYZXLaw, xyxzy, xyyzx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- The component-preserving closed crossing `x y x y = x y y x`. -/
theorem derivesClosedEvenSwitch (x y : Word Nat) :
    Derives basis
      (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have base : Derives basis xyxy xyyx :=
    Derives.fromBasis (e := xyxyXYYXLaw) (by simp [basis])
  have substituted :=
    Derives.subst base (instantiateThreeWords x y y)
  simpa [xyxyXYYXLaw, xyxy, xyyx, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Swap adjacent interior blocks while retaining a nonempty trailing block
and matching envelope blocks. -/
theorem derivesAdjacentInteriorBlockSwap
    (anchor left right trailing : Word Nat) :
    Derives basis
      ((((anchor ++ left) ++ right) ++ trailing) ++ anchor)
      ((((anchor ++ right) ++ left) ++ trailing) ++ anchor) := by
  have first :
      Derives basis
        ((((anchor ++ left) ++ right) ++ trailing) ++ anchor)
        ((((((anchor ++ anchor) ++ anchor) ++ left) ++ right) ++
          trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      derivesLeftEnvelopePower anchor ((left ++ right) ++ trailing)
  have second :
      Derives basis
        ((((((anchor ++ anchor) ++ anchor) ++ left) ++ right) ++
          trailing) ++ anchor)
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ left) ++
          right) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend anchor
        (derivesInteriorSwap anchor
          ((anchor ++ left) ++ right) trailing)
  have third :
      Derives basis
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ left) ++
          right) ++ anchor)
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ right) ++
          left) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((anchor ++ anchor) ++ trailing)
        (derivesInteriorSwap anchor left right)
  have fourth :
      Derives basis
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ right) ++
          left) ++ anchor)
        ((((((anchor ++ anchor) ++ anchor) ++ right) ++ left) ++
          trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend anchor
        (derivesInteriorSwap anchor trailing
          ((anchor ++ right) ++ left))
  have fifth :
      Derives basis
        ((((((anchor ++ anchor) ++ anchor) ++ right) ++ left) ++
          trailing) ++ anchor)
        ((((anchor ++ right) ++ left) ++ trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      (derivesLeftEnvelopePower anchor
        ((right ++ left) ++ trailing)).symm
  exact first.trans <| second.trans <| third.trans <| fourth.trans fifth

private theorem derivesRetainedCrossingBothNonempty
    (a b before after : Word Nat) :
    Derives basis
      (((((a ++ b) ++ before) ++ a) ++ after) ++ b)
      (((((a ++ b) ++ b) ++ before) ++ after) ++ a) := by
  have arrange :
      Derives basis
        (((((a ++ b) ++ before) ++ a) ++ after) ++ b)
        (((((a ++ b) ++ a) ++ before) ++ after) ++ b) := by
    simpa [Word.append_assoc] using
      Derives.prepend a
        (derivesAdjacentInteriorBlockSwap b before a after)
  have attach :
      Derives basis
        (((((a ++ b) ++ a) ++ before) ++ after) ++ b)
        (((((a ++ b) ++ b) ++ before) ++ after) ++ a) := by
    simpa [Word.append_assoc] using
      derivesAttachmentXYYZX a b (before ++ after)
  exact arrange.trans attach

private theorem derivesRetainedCrossingLeftEmpty
    (a b after : Word Nat) :
    Derives basis
      ((((a ++ b) ++ a) ++ after) ++ b)
      ((((a ++ b) ++ b) ++ after) ++ a) :=
  derivesAttachmentXYYZX a b after

private theorem derivesRetainedCrossingRightEmpty
    (a b before : Word Nat) :
    Derives basis
      ((((a ++ b) ++ before) ++ a) ++ b)
      ((((a ++ b) ++ b) ++ before) ++ a) := by
  have arrange :
      Derives basis
        ((((a ++ b) ++ before) ++ a) ++ b)
        ((((a ++ b) ++ a) ++ before) ++ b) := by
    simpa [Word.append_assoc] using
      Derives.prepend a (derivesInteriorSwap b before a)
  exact arrange.trans (derivesAttachmentXYYZX a b before)

private theorem derivesRetainedCrossingBothEmpty
    (a b : Word Nat) :
    Derives basis
      (((a ++ b) ++ a) ++ b)
      (((a ++ b) ++ b) ++ a) :=
  derivesClosedEvenSwitch a b

/-- Retain both crossing anchors while moving the suffix occurrence of the
second anchor into the envelope interior. The four empty/nonempty cases use
only component-preserving laws from the 20-law basis. -/
theorem listDerivesRetainedCrossing
    (a b : Word Nat) (before after : List Nat) :
    ListDerives
      (a.toList ++ b.toList ++ before ++ a.toList ++ after ++ b.toList)
      (a.toList ++ b.toList ++ b.toList ++ before ++ after ++ a.toList) := by
  cases before with
  | nil =>
      cases after with
      | nil =>
          simpa [Word.toList_append, List.append_assoc] using
            (ListDerives.ofWord
              (derivesRetainedCrossingBothEmpty a b))
      | cons afterHead afterTail =>
          let afterWord := S5_107.listWordOfCons afterHead afterTail
          simpa [afterWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesRetainedCrossingLeftEmpty a b afterWord))
  | cons beforeHead beforeTail =>
      let beforeWord := S5_107.listWordOfCons beforeHead beforeTail
      cases after with
      | nil =>
          simpa [beforeWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesRetainedCrossingRightEmpty a b beforeWord))
      | cons afterHead afterTail =>
          let afterWord := S5_107.listWordOfCons afterHead afterTail
          simpa [beforeWord, afterWord, S5_107.listWordOfCons,
            Word.toList, Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesRetainedCrossingBothNonempty
                  a b beforeWord afterWord))

private theorem derivesRetainedEndpointBothNonempty
    (anchor before after : Word Nat) :
    Derives basis
      ((((anchor ++ before) ++ anchor) ++ after) ++ anchor)
      ((((anchor ++ before) ++ after) ++ anchor) ++ anchor) := by
  have first :
      Derives basis
        ((((anchor ++ before) ++ anchor) ++ after) ++ anchor)
        ((((anchor ++ after) ++ before) ++ anchor) ++ anchor) := by
    simpa [Word.append_assoc] using
      derivesInteriorSwap anchor (before ++ anchor) after
  have second :
      Derives basis
        ((((anchor ++ after) ++ before) ++ anchor) ++ anchor)
        ((((anchor ++ before) ++ after) ++ anchor) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.appendRight
        (derivesInteriorSwap anchor after before) anchor
  exact first.trans second

/-- Move a later endpoint occurrence next to the closing endpoint pair. -/
theorem listDerivesRetainedEndpoint
    (anchor : Word Nat) (before after : List Nat) :
    ListDerives
      (anchor.toList ++ before ++ anchor.toList ++ after ++ anchor.toList)
      (anchor.toList ++ before ++ after ++ anchor.toList ++ anchor.toList) := by
  cases after with
  | nil =>
      simpa [List.append_assoc] using
        (ListDerives.refl
          (anchor.toList ++ before ++ anchor.toList ++ anchor.toList))
  | cons afterHead afterTail =>
      let afterWord := S5_107.listWordOfCons afterHead afterTail
      cases before with
      | nil =>
          simpa [afterWord, S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesEndpointTransfer anchor afterWord))
      | cons beforeHead beforeTail =>
          let beforeWord := S5_107.listWordOfCons beforeHead beforeTail
          simpa [beforeWord, afterWord, S5_107.listWordOfCons,
            Word.toList, Word.toList_append, List.append_assoc] using
              (ListDerives.ofWord
                (derivesRetainedEndpointBothNonempty
                  anchor beforeWord afterWord))

/-- Swap two nonempty leading interior blocks while retaining an arbitrary
interior tail and suffix after the closing endpoint. -/
theorem listDerivesParityEnvelopeBlockSwap
    (endpoint leftHead rightHead : Nat)
    (leftTail rightTail trailing suffix : List Nat) :
    ListDerives
      (S5_441.parityEnvelopeRender endpoint
        ((leftHead :: leftTail) ++
          (rightHead :: rightTail) ++ trailing) suffix)
      (S5_441.parityEnvelopeRender endpoint
        ((rightHead :: rightTail) ++
          (leftHead :: leftTail) ++ trailing) suffix) := by
  let anchor := Word.singleton endpoint
  let left := S5_107.listWordOfCons leftHead leftTail
  let right := S5_107.listWordOfCons rightHead rightTail
  cases trailing with
  | nil =>
      simpa [S5_441.parityEnvelopeRender, anchor, left, right,
        S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          ListDerives.append
            (ListDerives.ofWord
              (derivesInteriorSwap anchor left right))
            suffix
  | cons trailingHead trailingTail =>
      let retained :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [S5_441.parityEnvelopeRender, anchor, left, right, retained,
        S5_107.listWordOfCons, Word.toList,
        Word.toList_singleton, List.append_assoc] using
          ListDerives.context [] suffix <|
            ListDerives.ofWord <|
              derivesAdjacentInteriorBlockSwap
                anchor left right retained

/-- Any permutation of an initial envelope-interior segment is derivable
while an arbitrary interior tail and outer suffix remain fixed. -/
theorem listDerivesParityEnvelopeInteriorPermutationWithTrailing
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    ∀ (trailing suffix : List Nat),
      ListDerives
        (S5_441.parityEnvelopeRender endpoint
          (left ++ trailing) suffix)
        (S5_441.parityEnvelopeRender endpoint
          (right ++ trailing) suffix) := by
  induction permutation with
  | nil =>
      intro trailing suffix
      exact ListDerives.refl _
  | @cons letter source target permutation ih =>
      intro trailing suffix
      cases source with
      | nil =>
          have targetEmpty : target = [] := permutation.nil_eq.symm
          subst target
          exact ListDerives.refl _
      | cons sourceHead sourceTail =>
          have targetNonempty : target ≠ [] := by
            intro targetEmpty
            subst target
            have lengthEq := permutation.length_eq
            simp at lengthEq
          obtain ⟨targetHead, targetTail, rfl⟩ :=
            List.exists_cons_of_ne_nil targetNonempty
          have moveHeadRight :=
            listDerivesParityEnvelopeBlockSwap
              endpoint letter sourceHead
              [] sourceTail trailing suffix
          have permuteTail := ih (letter :: trailing) suffix
          have permuteTail' :
              ListDerives
                (S5_441.parityEnvelopeRender endpoint
                  ((sourceHead :: sourceTail) ++
                    [letter] ++ trailing) suffix)
                (S5_441.parityEnvelopeRender endpoint
                  ((targetHead :: targetTail) ++
                    [letter] ++ trailing) suffix) := by
            simpa [List.append_assoc] using permuteTail
          have moveHeadLeft :=
            ListDerives.symm <|
              listDerivesParityEnvelopeBlockSwap
                endpoint letter targetHead
                [] targetTail trailing suffix
          simpa [List.append_assoc] using
            ListDerives.trans moveHeadRight <|
              ListDerives.trans permuteTail' moveHeadLeft
  | swap first second rest =>
      intro trailing suffix
      simpa [List.append_assoc] using
        listDerivesParityEnvelopeBlockSwap
          endpoint second first [] [] (rest ++ trailing) suffix
  | trans _ _ ihFirst ihSecond =>
      intro trailing suffix
      exact
        ListDerives.trans
          (ihFirst trailing suffix)
          (ihSecond trailing suffix)

/-- Any permutation of the full interior between matching endpoints is
derivable while the suffix after the closing endpoint remains fixed. -/
theorem listDerivesParityEnvelopeInteriorPermutation
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    ListDerives
      (S5_441.parityEnvelopeRender endpoint left suffix)
      (S5_441.parityEnvelopeRender endpoint right suffix) := by
  simpa using
    listDerivesParityEnvelopeInteriorPermutationWithTrailing
      endpoint permutation [] suffix

private theorem replayParityEnvelopeCrossing
    {endpoint crossing : Nat}
    {interior middle before after : List Nat}
    (arrange : interior.Perm (crossing :: middle)) :
    ListDerives
      (S5_441.parityEnvelopeRender endpoint interior
        (before ++ crossing :: after))
      (S5_441.parityEnvelopeRender endpoint
        (crossing :: crossing :: (middle ++ before)) after) := by
  have arrangeInterior :
      ListDerives
        (S5_441.parityEnvelopeRender endpoint interior
          (before ++ crossing :: after))
        (S5_441.parityEnvelopeRender endpoint
          (crossing :: middle)
          (before ++ crossing :: after)) :=
    listDerivesParityEnvelopeInteriorPermutation
      endpoint (before ++ crossing :: after) arrange
  have absorbCrossing :
      ListDerives
        (S5_441.parityEnvelopeRender endpoint
          (crossing :: middle)
          (before ++ crossing :: after))
        (S5_441.parityEnvelopeRender endpoint
          (crossing :: crossing :: (middle ++ before)) after) := by
    simpa [S5_441.parityEnvelopeRender, Word.toList_singleton,
      List.append_assoc] using
        ListDerives.append
          (listDerivesRetainedCrossing
            (Word.singleton endpoint)
            (Word.singleton crossing) middle before)
          after
  exact ListDerives.trans arrangeInterior absorbCrossing

private theorem replayParityEnvelopeEndpoint
    {endpoint : Nat} {interior before after : List Nat} :
    ListDerives
      (S5_441.parityEnvelopeRender endpoint interior
        (before ++ endpoint :: after))
      (S5_441.parityEnvelopeRender endpoint
        (interior ++ before ++ [endpoint]) after) := by
  simpa [S5_441.parityEnvelopeRender, Word.toList_singleton,
    List.append_assoc] using
      ListDerives.append
        (listDerivesRetainedEndpoint
          (Word.singleton endpoint) interior before)
        after

/-- Replay one abstract parity-envelope transition using only the S5_442
20-law basis. -/
theorem parityEnvelopeStepReplay
    {endpoint : Nat}
    {interior suffix nextInterior nextSuffix : List Nat}
    (step :
      S5_441.ParityEnvelopeStep endpoint
        interior suffix nextInterior nextSuffix) :
    ListDerives
      (S5_441.parityEnvelopeRender endpoint interior suffix)
      (S5_441.parityEnvelopeRender endpoint
        nextInterior nextSuffix) := by
  cases step with
  | crossing arrange => exact replayParityEnvelopeCrossing arrange
  | endpoint => exact replayParityEnvelopeEndpoint

/-- Replay a terminating abstract parity-envelope plan using the S5_442
basis. -/
theorem parityEnvelopePlanReplay
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      S5_441.ParityEnvelopePlan endpoint
        interior suffix finalInterior) :
    ListDerives
      (S5_441.parityEnvelopeRender endpoint interior suffix)
      (S5_441.parityEnvelopeRender endpoint finalInterior []) := by
  induction plan with
  | done current => exact ListDerives.refl _
  | advance step remaining ih =>
      exact ListDerives.trans (parityEnvelopeStepReplay step) ih

/-- Every support-connected component of length at least two derives to a
closed parity envelope at its first letter. The replay preserves the exact
multiset, not only support and parity. -/
theorem exists_parityEnvelopeDerivation_of_connected
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ finalInterior,
      ListDerives
          (head :: tail)
          (S5_441.parityEnvelopeRender head finalInterior []) ∧
        (head :: tail).Perm
          (S5_441.parityEnvelopeRender head finalInterior []) := by
  obtain
    ⟨interior, suffix, finalInterior, shape, _state, plan⟩ :=
      S5_441.exists_parityEnvelopePlan_of_connected
        connected lengthAtLeastTwo
  refine ⟨finalInterior, ?_, ?_⟩
  · rw [shape]
    exact parityEnvelopePlanReplay plan
  · rw [shape]
    exact S5_441.ParityEnvelopePlan.render_perm plan

end SemigroupBasis.CoRoots.S5_442

import SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions

/-!
# Lee--Zhang Condition 7: unrestricted completeness

This module formalizes the normal-form argument in Lee--Zhang, Section 5.
The four displayed laws preserve support, global simplicity, and occurrence
parity.  A connected component is first gathered into a closed endpoint
envelope without changing its multiset.  Its multiplicities are then reduced
to one for a singleton, two for a positive even count, and three for a larger
odd count.  The `S5_379` factor fixes the ordered component supports and the
globally simple variables, while the cyclic factor fixes occurrence parity.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangCondition7Completeness

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions

private abbrev B : List (Identity Nat) := Condition7.basis

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives B

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def xxxx : Word Nat := w 0 [0, 0, 0]
private def xx : Word Nat := w 0 [0]
private def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
private def xyx : Word Nat := w 0 [1, 0]
private def xyyx : Word Nat := w 0 [1, 1, 0]
private def yxxy : Word Nat := w 1 [0, 0, 1]
private def xyzx : Word Nat := w 0 [1, 2, 0]
private def xzyx : Word Nat := w 0 [2, 1, 0]

private def powerLaw : Identity Nat := ⟨xxxx, xx⟩
private def leftEnvelopeLaw : Identity Nat := ⟨xxxyx, xyx⟩
private def endpointSwitchLaw : Identity Nat := ⟨xyyx, yxxy⟩
private def closedSwapLaw : Identity Nat := ⟨xyzx, xzyx⟩

private theorem basis_eq :
    B = [powerLaw, leftEnvelopeLaw, endpointSwitchLaw, closedSwapLaw] :=
  rfl

private theorem basisPower : Derives B xxxx xx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis_eq, powerLaw])

private theorem basisLeftEnvelope : Derives B xxxyx xyx :=
  Derives.fromBasis (e := leftEnvelopeLaw)
    (by simp [basis_eq, leftEnvelopeLaw])

private theorem basisEndpointSwitch : Derives B xyyx yxxy :=
  Derives.fromBasis (e := endpointSwitchLaw)
    (by simp [basis_eq, endpointSwitchLaw])

private theorem basisClosedSwap : Derives B xyzx xzyx :=
  Derives.fromBasis (e := closedSwapLaw)
    (by simp [basis_eq, closedSwapLaw])

private def instantiateThreeWords
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

/-- The first Condition 7 law under an arbitrary nonempty substitution. -/
private theorem derivesFourToTwo (block : Word Nat) :
    Derives B (((block ++ block) ++ block) ++ block) (block ++ block) := by
  have substituted :=
    Derives.subst basisPower
      (instantiateThreeWords block block block)
  simpa [xxxx, xx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The second Condition 7 law under an arbitrary nonempty substitution. -/
private theorem derivesLeftEnvelopeContraction
    (anchor middle : Word Nat) :
    Derives B
      ((((anchor ++ anchor) ++ anchor) ++ middle) ++ anchor)
      ((anchor ++ middle) ++ anchor) := by
  have substituted :=
    Derives.subst basisLeftEnvelope
      (instantiateThreeWords anchor middle middle)
  simpa [xxxyx, xyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The third Condition 7 law under an arbitrary nonempty substitution. -/
private theorem derivesEndpointSwitch (left right : Word Nat) :
    Derives B
      (((left ++ right) ++ right) ++ left)
      (((right ++ left) ++ left) ++ right) := by
  have substituted :=
    Derives.subst basisEndpointSwitch
      (instantiateThreeWords left right right)
  simpa [xyyx, yxxy, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- The fourth Condition 7 law under an arbitrary nonempty substitution. -/
private theorem derivesInteriorSwap
    (anchor left right : Word Nat) :
    Derives B
      (((anchor ++ left) ++ right) ++ anchor)
      (((anchor ++ right) ++ left) ++ anchor) := by
  have substituted :=
    Derives.subst basisClosedSwap
      (instantiateThreeWords anchor left right)
  simpa [xyzx, xzyx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Adjacent nonempty interior blocks can be swapped while a nonempty
trailing interior block is retained.  The temporary three anchor copies are
introduced and removed by `x^3 H x = x H x`. -/
private theorem derivesAdjacentInteriorBlockSwap
    (anchor left right trailing : Word Nat) :
    Derives B
      ((((anchor ++ left) ++ right) ++ trailing) ++ anchor)
      ((((anchor ++ right) ++ left) ++ trailing) ++ anchor) := by
  have first :
      Derives B
        ((((anchor ++ left) ++ right) ++ trailing) ++ anchor)
        ((((((anchor ++ anchor) ++ anchor) ++ left) ++ right) ++
          trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      (derivesLeftEnvelopeContraction anchor
        ((left ++ right) ++ trailing)).symm
  have second :
      Derives B
        ((((((anchor ++ anchor) ++ anchor) ++ left) ++ right) ++
          trailing) ++ anchor)
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ left) ++
          right) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend anchor
        (derivesInteriorSwap anchor
          ((anchor ++ left) ++ right) trailing)
  have third :
      Derives B
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ left) ++
          right) ++ anchor)
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ right) ++
          left) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((anchor ++ anchor) ++ trailing)
        (derivesInteriorSwap anchor left right)
  have fourth :
      Derives B
        ((((((anchor ++ anchor) ++ trailing) ++ anchor) ++ right) ++
          left) ++ anchor)
        ((((((anchor ++ anchor) ++ anchor) ++ right) ++ left) ++
          trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend anchor
        (derivesInteriorSwap anchor trailing
          ((anchor ++ right) ++ left))
  have fifth :
      Derives B
        ((((((anchor ++ anchor) ++ anchor) ++ right) ++ left) ++
          trailing) ++ anchor)
        ((((anchor ++ right) ++ left) ++ trailing) ++ anchor) := by
    simpa [Word.append_assoc] using
      derivesLeftEnvelopeContraction anchor
        ((right ++ left) ++ trailing)
  exact first.trans <| second.trans <| third.trans <| fourth.trans fifth

private def envelopeRender
    (endpoint : Nat) (interior suffix : List Nat) : List Nat :=
  endpoint :: interior ++ endpoint :: suffix

@[simp]
private theorem envelopeRender_nil
    (endpoint : Nat) (interior : List Nat) :
    envelopeRender endpoint interior [] =
      endpoint :: interior ++ [endpoint] := by
  simp [envelopeRender]

private theorem listDerivesEnvelopeBlockSwap
    (endpoint leftHead rightHead : Nat)
    (leftTail rightTail trailing suffix : List Nat) :
    ListDerives
      (envelopeRender endpoint
        ((leftHead :: leftTail) ++
          (rightHead :: rightTail) ++ trailing) suffix)
      (envelopeRender endpoint
        ((rightHead :: rightTail) ++
          (leftHead :: leftTail) ++ trailing) suffix) := by
  let anchor := Word.singleton endpoint
  let left := S5_107.listWordOfCons leftHead leftTail
  let right := S5_107.listWordOfCons rightHead rightTail
  cases trailing with
  | nil =>
      simpa [envelopeRender, anchor, left, right,
        S5_107.listWordOfCons, Word.toList,
        Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
          (S5_107.ListDerives.ofWord
            (derivesInteriorSwap anchor left right)).append suffix
  | cons trailingHead trailingTail =>
      let retained :=
        S5_107.listWordOfCons trailingHead trailingTail
      simpa [envelopeRender, anchor, left, right, retained,
        S5_107.listWordOfCons, Word.toList,
        Word.toList_singleton, List.append_assoc] using
          (S5_107.ListDerives.ofWord
            (derivesAdjacentInteriorBlockSwap
              anchor left right retained)).append suffix

/-- Every permutation of an endpoint-envelope interior is derivable while
the post-envelope suffix remains fixed. -/
private theorem listDerivesInteriorPermutationWithTrailing
    (endpoint : Nat) {left right : List Nat}
    (permutation : left.Perm right) :
    forall (trailing suffix : List Nat),
      ListDerives
        (envelopeRender endpoint (left ++ trailing) suffix)
        (envelopeRender endpoint (right ++ trailing) suffix) := by
  induction permutation with
  | nil =>
      intro trailing suffix
      exact S5_107.ListDerives.refl _
  | @cons letter source target permutation ih =>
      intro trailing suffix
      cases source with
      | nil =>
          have targetEmpty : target = [] := permutation.nil_eq.symm
          subst target
          exact S5_107.ListDerives.refl _
      | cons sourceHead sourceTail =>
          have targetNonempty : target ≠ [] := by
            intro targetEmpty
            subst target
            have lengthEq := permutation.length_eq
            simp at lengthEq
          obtain ⟨targetHead, targetTail, rfl⟩ :=
            List.exists_cons_of_ne_nil targetNonempty
          have moveHeadRight :=
            listDerivesEnvelopeBlockSwap
              endpoint letter sourceHead
              [] sourceTail trailing suffix
          have permuteTail := ih (letter :: trailing) suffix
          have permuteTail' :
              ListDerives
                (envelopeRender endpoint
                  ((sourceHead :: sourceTail) ++
                    [letter] ++ trailing) suffix)
                (envelopeRender endpoint
                  ((targetHead :: targetTail) ++
                    [letter] ++ trailing) suffix) := by
            simpa [List.append_assoc] using permuteTail
          have moveHeadLeft :=
            (listDerivesEnvelopeBlockSwap
              endpoint letter targetHead
              [] targetTail trailing suffix).symm
          simpa [List.append_assoc] using
            moveHeadRight.trans (permuteTail'.trans moveHeadLeft)
  | swap first second rest =>
      intro trailing suffix
      simpa [List.append_assoc] using
        listDerivesEnvelopeBlockSwap
          endpoint second first [] [] (rest ++ trailing) suffix
  | trans _ _ first second =>
      intro trailing suffix
      exact (first trailing suffix).trans (second trailing suffix)

private theorem listDerivesInteriorPermutation
    (endpoint : Nat) (suffix : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    ListDerives
      (envelopeRender endpoint left suffix)
      (envelopeRender endpoint right suffix) := by
  simpa using
    listDerivesInteriorPermutationWithTrailing
      endpoint permutation [] suffix

/-- Add two copies at the left edge of a closed endpoint envelope.  The
empty-middle case is the separate law `x^4 = x^2`. -/
private theorem listDerivesLeftEnvelopeExpansion
    (endpoint : Nat) (middle suffix : List Nat) :
    ListDerives
      (envelopeRender endpoint middle suffix)
      (envelopeRender endpoint
        ([endpoint, endpoint] ++ middle) suffix) := by
  cases middle with
  | nil =>
      simpa [envelopeRender, Word.toList_append,
        Word.toList_singleton, List.append_assoc] using
        (S5_107.ListDerives.ofWord
          (derivesFourToTwo (Word.singleton endpoint)).symm).append suffix
  | cons middleHead middleTail =>
      let middleWord :=
        S5_107.listWordOfCons middleHead middleTail
      simpa [envelopeRender, middleWord, S5_107.listWordOfCons,
        Word.toList, Word.toList_append, Word.toList_singleton,
        List.append_assoc] using
        (S5_107.ListDerives.ofWord
          (derivesLeftEnvelopeContraction
            (Word.singleton endpoint) middleWord).symm).append suffix

/-- Add two copies at the right edge of a closed endpoint envelope. -/
private theorem listDerivesRightEnvelopeExpansion
    (endpoint : Nat) (middle suffix : List Nat) :
    ListDerives
      (envelopeRender endpoint middle suffix)
      (envelopeRender endpoint
        (middle ++ [endpoint, endpoint]) suffix) := by
  have expand :=
    listDerivesLeftEnvelopeExpansion endpoint middle suffix
  have permutation :
      ([endpoint, endpoint] ++ middle).Perm
        (middle ++ [endpoint, endpoint]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    omega
  exact expand.trans
    (listDerivesInteriorPermutation endpoint suffix permutation)

/-! ## Lee--Zhang Lemma 5.2(c) -/

/-- The first crossing law from Lee--Zhang Lemma 5.2(c):
`x H y K x y = x H y K y x`.  Every intermediate word preserves support,
global simplicity, and parity. -/
private theorem listDerivesCrossingRight
    (x y : Nat) (h k : List Nat) :
    ListDerives
      (x :: h ++ y :: k ++ [x, y])
      (x :: h ++ y :: k ++ [y, x]) := by
  have expandX :
      ListDerives
        (x :: h ++ y :: k ++ [x, y])
        (x :: x :: x :: h ++ y :: k ++ [x, y]) := by
    simpa [envelopeRender, List.append_assoc] using
      listDerivesLeftEnvelopeExpansion x (h ++ y :: k) [y]
  have expandY :
      ListDerives
        (x :: x :: x :: h ++ y :: k ++ [x, y])
        (x :: x :: x :: h ++ y :: y :: y :: k ++ [x, y]) := by
    simpa [envelopeRender, List.append_assoc] using
      (listDerivesLeftEnvelopeExpansion y (k ++ [x]) []).prepend
        ([x, x, x] ++ h)
  have xPermutation :
      ([x, x] ++ h ++ [y, y, y] ++ k).Perm
        ([x] ++ h ++ [y, y, y] ++ k ++ [x]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have moveX :
      ListDerives
        (x :: x :: x :: h ++ y :: y :: y :: k ++ [x, y])
        (x :: x :: h ++ y :: y :: y :: k ++ [x, x, y]) := by
    simpa [envelopeRender, List.append_assoc] using
      listDerivesInteriorPermutation x [y] xPermutation
  have yPermutation :
      ([y, y] ++ k ++ [x, x]).Perm
        ([y] ++ k ++ [y, x, x]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have moveY :
      ListDerives
        (x :: x :: h ++ y :: y :: y :: k ++ [x, x, y])
        (x :: x :: h ++ y :: y :: k ++ [y, x, x, y]) := by
    simpa [envelopeRender, List.append_assoc] using
      (listDerivesInteriorPermutation y [] yPermutation).prepend
        ([x, x] ++ h)
  have switch :
      ListDerives
        (x :: x :: h ++ y :: y :: k ++ [y, x, x, y])
        (x :: x :: h ++ y :: y :: k ++ [x, y, y, x]) := by
    simpa [Word.toList_append, Word.toList_singleton,
      List.append_assoc] using
      (S5_107.ListDerives.ofWord
        (derivesEndpointSwitch
          (Word.singleton x) (Word.singleton y)).symm).prepend
          ([x, x] ++ h ++ [y, y] ++ k)
  have xPermutation' :
      ([x] ++ h ++ [y, y] ++ k ++ [x, y, y]).Perm
        ([x, x] ++ h ++ [y, y] ++ k ++ [y, y]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have moveX' :
      ListDerives
        (x :: x :: h ++ y :: y :: k ++ [x, y, y, x])
        (x :: x :: x :: h ++ y :: y :: k ++ [y, y, x]) := by
    simpa [envelopeRender, List.append_assoc] using
      listDerivesInteriorPermutation x [] xPermutation'
  have yPermutation' :
      ([y] ++ k ++ [y]).Perm ([y, y] ++ k) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have moveY' :
      ListDerives
        (x :: x :: x :: h ++ y :: y :: k ++ [y, y, x])
        (x :: x :: x :: h ++ y :: y :: y :: k ++ [y, x]) := by
    simpa [envelopeRender, List.append_assoc] using
      (listDerivesInteriorPermutation y [x] yPermutation').prepend
        ([x, x, x] ++ h)
  have contractX :
      ListDerives
        (x :: x :: x :: h ++ y :: y :: y :: k ++ [y, x])
        (x :: h ++ y :: y :: y :: k ++ [y, x]) := by
    simpa [envelopeRender, List.append_assoc] using
      (listDerivesLeftEnvelopeExpansion x
        (h ++ [y, y, y] ++ k ++ [y]) []).symm
  have contractY :
      ListDerives
        (x :: h ++ y :: y :: y :: k ++ [y, x])
        (x :: h ++ y :: k ++ [y, x]) := by
    simpa [envelopeRender, List.append_assoc] using
      ((listDerivesLeftEnvelopeExpansion y k []).symm.context
        (x :: h) [x])
  exact expandX.trans <| expandY.trans <| moveX.trans <|
    moveY.trans <| switch.trans <| moveX'.trans <|
      moveY'.trans <| contractX.trans contractY

/-- The symmetric crossing law from Lee--Zhang Lemma 5.2(c):
`x y H x K y = y x H x K y`. -/
private theorem listDerivesCrossingLeft
    (x y : Nat) (h k : List Nat) :
    ListDerives
      (x :: y :: h ++ x :: k ++ [y])
      (y :: x :: h ++ x :: k ++ [y]) := by
  have expandX :
      ListDerives
        (x :: y :: h ++ x :: k ++ [y])
        (x :: y :: h ++ x :: x :: x :: k ++ [y]) := by
    simpa [envelopeRender, List.append_assoc] using
      listDerivesRightEnvelopeExpansion x (y :: h) (k ++ [y])
  have expandY :
      ListDerives
        (x :: y :: h ++ x :: x :: x :: k ++ [y])
        (x :: y :: h ++ x :: x :: x :: k ++ [y, y, y]) := by
    simpa [envelopeRender, List.append_assoc] using
      (listDerivesRightEnvelopeExpansion y
        (h ++ [x, x, x] ++ k) []).prepend [x]
  have yPermutation :
      (h ++ [x, x, x] ++ k ++ [y, y]).Perm
        ([y, x] ++ h ++ [x, x] ++ k ++ [y]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have arrange :
      ListDerives
        (x :: y :: h ++ x :: x :: x :: k ++ [y, y, y])
        (x :: y :: y :: x :: h ++ x :: x :: k ++ [y, y]) := by
    simpa [envelopeRender, List.append_assoc] using
      (listDerivesInteriorPermutation y [] yPermutation).prepend [x]
  have switch :
      ListDerives
        (x :: y :: y :: x :: h ++ x :: x :: k ++ [y, y])
        (y :: x :: x :: y :: h ++ x :: x :: k ++ [y, y]) := by
    simpa [Word.toList_append, Word.toList_singleton,
      List.append_assoc] using
      (S5_107.ListDerives.ofWord
        (derivesEndpointSwitch
          (Word.singleton x) (Word.singleton y))).append
            (h ++ [x, x] ++ k ++ [y, y])
  have yPermutation' :
      ([x, x, y] ++ h ++ [x, x] ++ k ++ [y]).Perm
        ([x] ++ h ++ [x, x, x] ++ k ++ [y, y]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have arrange' :
      ListDerives
        (y :: x :: x :: y :: h ++ x :: x :: k ++ [y, y])
        (y :: x :: h ++ x :: x :: x :: k ++ [y, y, y]) := by
    simpa [envelopeRender, List.append_assoc] using
      listDerivesInteriorPermutation y [] yPermutation'
  have contractX :
      ListDerives
        (y :: x :: h ++ x :: x :: x :: k ++ [y, y, y])
        (y :: x :: h ++ x :: k ++ [y, y, y]) := by
    simpa [envelopeRender, List.append_assoc] using
      ((listDerivesRightEnvelopeExpansion x h
        (k ++ [y, y, y])).symm.prepend [y])
  have contractY :
      ListDerives
        (y :: x :: h ++ x :: k ++ [y, y, y])
        (y :: x :: h ++ x :: k ++ [y]) := by
    simpa [envelopeRender, List.append_assoc] using
      (listDerivesRightEnvelopeExpansion y
        (x :: h ++ x :: k) []).symm
  exact expandX.trans <| expandY.trans <| arrange.trans <|
    switch.trans <| arrange'.trans <| contractX.trans contractY

/-- Retarget `x y^2 H x` to `y x^2 H y`, retaining the complete multiset. -/
private theorem listDerivesEnvelopeSwitch
    (oldEndpoint newEndpoint : Nat) (middle : List Nat) :
    ListDerives
      (oldEndpoint :: newEndpoint :: newEndpoint :: middle ++ [oldEndpoint])
      (newEndpoint :: oldEndpoint :: oldEndpoint :: middle ++ [newEndpoint]) := by
  have firstPermutation :
      (newEndpoint :: newEndpoint :: middle).Perm
        (newEndpoint :: middle ++ [newEndpoint]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have first :=
    listDerivesInteriorPermutation oldEndpoint [] firstPermutation
  have second :=
    (listDerivesCrossingRight oldEndpoint newEndpoint [] middle).symm
  have third :=
    listDerivesCrossingLeft oldEndpoint newEndpoint middle []
  have finalPermutation :
      (oldEndpoint :: middle ++ [oldEndpoint]).Perm
        (oldEndpoint :: oldEndpoint :: middle) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have fourth :=
    listDerivesInteriorPermutation newEndpoint [] finalPermutation
  have remaining :
      ListDerives
        ([oldEndpoint] ++ newEndpoint :: middle ++ [oldEndpoint, newEndpoint])
        (envelopeRender newEndpoint
          (oldEndpoint :: oldEndpoint :: middle) []) := by
    simpa [List.append_assoc] using third.trans fourth
  have afterFirst :
      ListDerives
        (envelopeRender oldEndpoint
          (newEndpoint :: newEndpoint :: middle) [])
        ([oldEndpoint] ++ newEndpoint :: middle ++
          [newEndpoint, oldEndpoint]) := by
    simpa [envelopeRender, List.append_assoc] using first
  simpa [envelopeRender, List.append_assoc] using
    afterFirst.trans (second.trans remaining)

/-! ## Exact-multiset connected envelopes -/

private theorem envelopeStateAbsorbCrossing
    {endpoint crossing : Nat}
    {interior before after : List Nat}
    (state :
      ConnectedComponentEnvelopeState endpoint interior
        (before ++ crossing :: after))
    (arrange : interior.Perm (crossing :: interior.erase crossing)) :
    ConnectedComponentEnvelopeState endpoint
      (crossing :: crossing :: (interior.erase crossing ++ before))
      after := by
  have base :=
    state.peelInterior
      (by
        have member : crossing ∈ crossing :: interior.erase crossing := by
          simp
        exact arrange.mem_iff.mpr member)
      rfl
  refine ⟨?_⟩
  intro left right afterShape rightNonempty
  obtain ⟨value, prefixMember, rightMember⟩ :=
    base.linked left right afterShape rightNonempty
  refine ⟨value, ?_, rightMember⟩
  simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using
    prefixMember

private theorem envelopeStateAbsorbEndpoint
    {endpoint : Nat} {interior before after : List Nat}
    (state :
      ConnectedComponentEnvelopeState endpoint interior
        (before ++ endpoint :: after)) :
    ConnectedComponentEnvelopeState endpoint
      (interior ++ before ++ [endpoint]) after := by
  have base := state.peelEndpoint rfl
  refine ⟨?_⟩
  intro left right afterShape rightNonempty
  obtain ⟨value, prefixMember, rightMember⟩ :=
    base.linked left right afterShape rightNonempty
  refine ⟨value, ?_, rightMember⟩
  simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using
    prefixMember

private theorem listDerivesRetainedEndpoint
    (endpoint : Nat) (interior before after : List Nat) :
    ListDerives
      (envelopeRender endpoint interior
        (before ++ endpoint :: after))
      (envelopeRender endpoint
        (interior ++ before ++ [endpoint]) after) := by
  have permutation :
      (interior ++ endpoint :: before).Perm
        (interior ++ before ++ [endpoint]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  simpa [envelopeRender, List.append_assoc] using
    listDerivesInteriorPermutation endpoint after permutation

private theorem listDerivesRetainedCrossing
    (endpoint crossing : Nat) (middle before after : List Nat) :
    ListDerives
      (envelopeRender endpoint (crossing :: middle)
        (before ++ crossing :: after))
      (envelopeRender endpoint
        (crossing :: crossing :: (middle ++ before)) after) := by
  have firstPermutation :
      (middle ++ endpoint :: before).Perm
        (middle ++ before ++ [endpoint]) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have first :
      ListDerives
        (envelopeRender endpoint (crossing :: middle)
          (before ++ crossing :: after))
        (endpoint :: crossing :: middle ++ before ++
          [endpoint, crossing] ++ after) := by
    simpa [envelopeRender, List.append_assoc] using
      (listDerivesInteriorPermutation crossing after
        firstPermutation).prepend [endpoint]
  have second :
      ListDerives
        (endpoint :: crossing :: middle ++ before ++
          [endpoint, crossing] ++ after)
        (endpoint :: crossing :: middle ++ before ++
          [crossing, endpoint] ++ after) := by
    simpa [List.append_assoc] using
      (listDerivesCrossingRight endpoint crossing []
        (middle ++ before)).append after
  have finalPermutation :
      (crossing :: middle ++ before ++ [crossing]).Perm
        (crossing :: crossing :: (middle ++ before)) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append, List.count_cons,
      List.count_nil]
    omega
  have third :=
    listDerivesInteriorPermutation endpoint after finalPermutation
  have remaining :
      ListDerives
        (endpoint :: crossing :: middle ++ before ++
          [crossing, endpoint] ++ after)
        (envelopeRender endpoint
          (crossing :: crossing :: (middle ++ before)) after) := by
    simpa [envelopeRender, List.append_assoc] using third
  simpa [envelopeRender, List.append_assoc] using
    first.trans (second.trans remaining)

private theorem existsExactEnvelopeAux {endpoint : Nat} :
    forall (interior suffix : List Nat),
      ConnectedComponentEnvelopeState endpoint interior suffix →
        ∃ finalInterior,
          ListDerives
            (envelopeRender endpoint interior suffix)
            (envelopeRender endpoint finalInterior []) /\
          (envelopeRender endpoint interior suffix).Perm
            (envelopeRender endpoint finalInterior []) := by
  intro interior suffix state
  by_cases suffixEmpty : suffix = []
  · subst suffix
    exact ⟨interior, S5_107.ListDerives.refl _, List.Perm.refl _⟩
  · obtain ⟨letter, endpointOrInterior, letterInSuffix⟩ :=
      state.exists_crossing suffixEmpty
    obtain ⟨before, after, suffixShape⟩ :=
      List.append_of_mem letterInSuffix
    rcases endpointOrInterior with endpointEq | letterInInterior
    · subst letter
      subst suffix
      have nextState := envelopeStateAbsorbEndpoint state
      obtain ⟨finalInterior, remaining, remainingPerm⟩ :=
        existsExactEnvelopeAux
          (interior ++ before ++ [endpoint]) after nextState
      have step :=
        listDerivesRetainedEndpoint endpoint interior before after
      have stepPerm :
          (envelopeRender endpoint interior
              (before ++ endpoint :: after)).Perm
            (envelopeRender endpoint
              (interior ++ before ++ [endpoint]) after) := by
        rw [List.perm_iff_count]
        intro tested
        simp only [envelopeRender, List.count_append,
          List.count_cons, List.count_nil]
        omega
      exact
        ⟨finalInterior, step.trans remaining,
          stepPerm.trans remainingPerm⟩
    · subst suffix
      have arrange :
          interior.Perm (letter :: interior.erase letter) :=
        List.perm_cons_erase letterInInterior
      have nextState :=
        envelopeStateAbsorbCrossing state arrange
      obtain ⟨finalInterior, remaining, remainingPerm⟩ :=
        existsExactEnvelopeAux
          (letter :: letter :: (interior.erase letter ++ before))
          after nextState
      have arrangeDerivation :=
        listDerivesInteriorPermutation endpoint
          (before ++ letter :: after) arrange
      have crossingDerivation :=
        listDerivesRetainedCrossing endpoint letter
          (interior.erase letter) before after
      have step :
          ListDerives
            (envelopeRender endpoint interior
              (before ++ letter :: after))
            (envelopeRender endpoint
              (letter :: letter ::
                (interior.erase letter ++ before)) after) := by
        exact arrangeDerivation.trans crossingDerivation
      have stepPerm :
          (envelopeRender endpoint interior
              (before ++ letter :: after)).Perm
            (envelopeRender endpoint
              (letter :: letter ::
                (interior.erase letter ++ before)) after) := by
        rw [List.perm_iff_count]
        intro tested
        have counts := (List.perm_iff_count.mp arrange) tested
        simp only [envelopeRender, List.count_append,
          List.count_cons] at counts ⊢
        omega
      exact
        ⟨finalInterior, step.trans remaining,
          stepPerm.trans remainingPerm⟩
termination_by interior suffix _state => suffix.length

/-- Every support-connected list of length at least two derives to a closed
endpoint envelope with exactly the same multiset. -/
private theorem existsExactEnvelopeOfConnected
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length) :
    ∃ finalInterior,
      ListDerives
        (head :: tail)
        (envelopeRender head finalInterior []) /\
      (head :: tail).Perm
        (envelopeRender head finalInterior []) := by
  obtain ⟨interior, suffix, shape, state⟩ :=
    connectedComponent_exists_initial_envelope
      connected lengthAtLeastTwo
  obtain ⟨finalInterior, derivation, permutation⟩ :=
    existsExactEnvelopeAux interior suffix state
  rw [shape]
  exact ⟨finalInterior, derivation, permutation⟩

/-! ## Threshold-parity multiplicity normalization -/

private def endpointCopies (endpoint tested : Nat) : Nat :=
  [endpoint, endpoint].count tested

private theorem endpointCopies_le_two (endpoint tested : Nat) :
    endpointCopies endpoint tested ≤ 2 := by
  by_cases same : endpoint = tested <;> simp [endpointCopies, same]

private theorem count_envelopeRender
    (endpoint tested : Nat) (interior : List Nat) :
    (envelopeRender endpoint interior []).count tested =
      endpointCopies endpoint tested + interior.count tested := by
  by_cases same : endpoint = tested
  · subst tested
    simp [envelopeRender, endpointCopies, List.count_append]
    omega
  · simp [envelopeRender, endpointCopies, same, List.count_append]

/-- Retain one copy of a singleton, two copies of a positive even
multiplicity, and three copies of a larger odd multiplicity, counting the
two protected endpoint copies as part of the whole word. -/
private def endpointThresholdReduce
    (endpoint : Nat) : List Nat → List Nat
  | [] => []
  | letter :: rest =>
      let reduced := endpointThresholdReduce endpoint rest
      if endpointCopies endpoint letter + reduced.count letter < 3 then
        letter :: reduced
      else
        reduced.erase letter

private theorem endpointThresholdReduce_total_le_three
    (endpoint tested : Nat) (interior : List Nat) :
    endpointCopies endpoint tested +
        (endpointThresholdReduce endpoint interior).count tested ≤ 3 := by
  induction interior with
  | nil =>
      have bound := endpointCopies_le_two endpoint tested
      simp [endpointThresholdReduce]
      omega
  | cons letter rest ih =>
      simp only [endpointThresholdReduce]
      split <;> rename_i countCondition
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal)]
          exact ih
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_erase_self]
          have endpointBound := endpointCopies_le_two endpoint letter
          omega
        · rw [List.count_erase_of_ne equal]
          exact ih

private theorem endpointThresholdReduce_total_mod_two
    (endpoint tested : Nat) (interior : List Nat) :
    (endpointCopies endpoint tested +
        (endpointThresholdReduce endpoint interior).count tested) % 2 =
      (endpointCopies endpoint tested + interior.count tested) % 2 := by
  induction interior with
  | nil =>
      simp [endpointThresholdReduce]
  | cons letter rest ih =>
      simp only [endpointThresholdReduce]
      split <;> rename_i countCondition
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal)]
          exact ih
      · by_cases equal : tested = letter
        · subst tested
          have totalBound :=
            endpointThresholdReduce_total_le_three
              endpoint letter rest
          have endpointBound := endpointCopies_le_two endpoint letter
          have totalEq :
              endpointCopies endpoint letter +
                  (endpointThresholdReduce endpoint rest).count letter = 3 := by
            omega
          rw [List.count_erase_self, List.count_cons_self]
          omega
        · rw [List.count_erase_of_ne equal,
            List.count_cons_of_ne (Ne.symm equal)]
          exact ih

private theorem endpointThresholdReduce_total_capped
    (endpoint tested : Nat) (interior : List Nat) :
    min
        (endpointCopies endpoint tested +
          (endpointThresholdReduce endpoint interior).count tested) 2 =
      min (endpointCopies endpoint tested + interior.count tested) 2 := by
  induction interior with
  | nil =>
      simp [endpointThresholdReduce]
  | cons letter rest ih =>
      simp only [endpointThresholdReduce]
      split <;> rename_i countCondition
      · by_cases equal : tested = letter
        · subst tested
          rw [List.count_cons_self, List.count_cons_self]
          have totalBound :=
            endpointThresholdReduce_total_le_three
              endpoint letter rest
          omega
        · rw [List.count_cons_of_ne (Ne.symm equal),
            List.count_cons_of_ne (Ne.symm equal)]
          exact ih
      · by_cases equal : tested = letter
        · subst tested
          have totalBound :=
            endpointThresholdReduce_total_le_three
              endpoint letter rest
          have endpointBound := endpointCopies_le_two endpoint letter
          have totalEq :
              endpointCopies endpoint letter +
                  (endpointThresholdReduce endpoint rest).count letter = 3 := by
            omega
          rw [List.count_erase_self, List.count_cons_self]
          omega
        · rw [List.count_erase_of_ne equal,
            List.count_cons_of_ne (Ne.symm equal)]
          exact ih

private theorem listDerivesDeleteInteriorPair
    (endpoint letter : Nat) (pre reduced : List Nat)
    (countEq : reduced.count letter = 3) :
    ListDerives
      (envelopeRender endpoint (pre ++ letter :: reduced) [])
      (envelopeRender endpoint (pre ++ reduced.erase letter) []) := by
  let remainder :=
    ((reduced.erase letter).erase letter).erase letter
  have firstErase : (reduced.erase letter).count letter = 2 := by
    rw [List.count_erase_self, countEq]
  have secondErase :
      ((reduced.erase letter).erase letter).count letter = 1 := by
    rw [List.count_erase_self, firstErase]
  have thirdErase : remainder.count letter = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, secondErase]
  have sourcePermutation :
      (pre ++ letter :: reduced).Perm
        ([letter, letter, letter, letter] ++ pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp [countEq, thirdErase]
      omega
    · simp [remainder, equal, Ne.symm equal]
  have targetPermutation :
      (pre ++ reduced.erase letter).Perm
        ([letter, letter] ++ pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = letter
    · subst tested
      simp [firstErase, thirdErase]
      omega
    · simp [remainder, equal, Ne.symm equal]
  have arrangeSource :=
    listDerivesInteriorPermutation endpoint [] sourcePermutation
  have contract :
      ListDerives
        (envelopeRender endpoint
          ([letter, letter, letter, letter] ++ pre ++ remainder) [])
        (envelopeRender endpoint
          ([letter, letter] ++ pre ++ remainder) []) := by
    simpa [envelopeRender, Word.toList_append,
      Word.toList_singleton, List.append_assoc] using
      (S5_107.ListDerives.ofWord
        (derivesFourToTwo (Word.singleton letter))).context
          [endpoint] (pre ++ remainder ++ [endpoint])
  have restoreTarget :=
    listDerivesInteriorPermutation endpoint [] targetPermutation.symm
  exact arrangeSource.trans (contract.trans restoreTarget)

private theorem listDerivesDeleteEndpointPair
    (endpoint : Nat) (pre reduced : List Nat)
    (countEq : reduced.count endpoint = 1) :
    ListDerives
      (envelopeRender endpoint (pre ++ endpoint :: reduced) [])
      (envelopeRender endpoint (pre ++ reduced.erase endpoint) []) := by
  let remainder := reduced.erase endpoint
  have remainderCount : remainder.count endpoint = 0 := by
    simp only [remainder]
    rw [List.count_erase_self, countEq]
  have sourcePermutation :
      (pre ++ endpoint :: reduced).Perm
        ([endpoint, endpoint] ++ pre ++ remainder) := by
    rw [List.perm_iff_count]
    intro tested
    simp only [List.count_append]
    by_cases equal : tested = endpoint
    · subst tested
      simp [countEq, remainderCount]
      omega
    · simp [remainder, equal, Ne.symm equal]
  have targetPermutation :
      (pre ++ reduced.erase endpoint).Perm (pre ++ remainder) := by
    simp [remainder]
  have arrangeSource :=
    listDerivesInteriorPermutation endpoint [] sourcePermutation
  have contract :=
    (listDerivesLeftEnvelopeExpansion endpoint
      (pre ++ remainder) []).symm
  have restoreTarget :=
    listDerivesInteriorPermutation endpoint [] targetPermutation.symm
  exact arrangeSource.trans (contract.trans restoreTarget)

private theorem listDerivesNormalizeInteriorAux (endpoint : Nat) :
    forall (pre interior : List Nat),
      ListDerives
        (envelopeRender endpoint (pre ++ interior) [])
        (envelopeRender endpoint
          (pre ++ endpointThresholdReduce endpoint interior) []) := by
  intro pre interior
  induction interior generalizing pre with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons letter rest ih =>
      have suffixNormal := ih (pre ++ [letter])
      let reduced := endpointThresholdReduce endpoint rest
      have firstStep :
          ListDerives
            (envelopeRender endpoint (pre ++ letter :: rest) [])
            (envelopeRender endpoint (pre ++ letter :: reduced) []) := by
        simpa [reduced, List.append_assoc] using suffixNormal
      by_cases countLt :
          endpointCopies endpoint letter + reduced.count letter < 3
      · have reducedEq :
            endpointThresholdReduce endpoint (letter :: rest) =
              letter :: reduced := by
          simp [endpointThresholdReduce, reduced, countLt]
        rw [reducedEq]
        exact firstStep
      · have totalLe :
            endpointCopies endpoint letter + reduced.count letter ≤ 3 := by
          simpa [reduced] using
            endpointThresholdReduce_total_le_three
              endpoint letter rest
        have totalEq :
            endpointCopies endpoint letter + reduced.count letter = 3 := by
          omega
        have reducedEq :
            endpointThresholdReduce endpoint (letter :: rest) =
              reduced.erase letter := by
          simp [endpointThresholdReduce, reduced, countLt]
        rw [reducedEq]
        by_cases equal : letter = endpoint
        · subst letter
          have reducedCount : reduced.count endpoint = 1 := by
            have endpointCount : endpointCopies endpoint endpoint = 2 := by
              simp [endpointCopies]
            omega
          exact firstStep.trans
            (listDerivesDeleteEndpointPair
              endpoint pre reduced reducedCount)
        · have reducedCount : reduced.count letter = 3 := by
            simpa [endpointCopies, equal, Ne.symm equal] using totalEq
          exact firstStep.trans
            (listDerivesDeleteInteriorPair
              endpoint letter pre reduced reducedCount)

private theorem listDerivesNormalizeInterior
    (endpoint : Nat) (interior : List Nat) :
    ListDerives
      (envelopeRender endpoint interior [])
      (envelopeRender endpoint
        (endpointThresholdReduce endpoint interior) []) := by
  simpa using listDerivesNormalizeInteriorAux endpoint [] interior

private structure ComponentNormal
    (source target : List Nat) : Prop where
  derives : ListDerives source target
  bounded : ∀ tested, target.count tested ≤ 3
  capped : ∀ tested,
    min (target.count tested) 2 = min (source.count tested) 2
  parity : ∀ tested,
    target.count tested % 2 = source.count tested % 2
  shape :
    target.length = 1 ∨
      ∃ endpoint interior,
        target = envelopeRender endpoint interior []

private theorem existsComponentNormal
    {component : List Nat} (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    ∃ target, ComponentNormal component target := by
  cases component with
  | nil => contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          refine ⟨[head], ?_⟩
          refine
            { derives := S5_107.ListDerives.refl _
              bounded := ?_
              capped := ?_
              parity := ?_
              shape := Or.inl (by simp) }
          · intro tested
            by_cases equal : tested = head
            · subst tested
              simp
            · rw [List.count_cons_of_ne (Ne.symm equal), List.count_nil]
              omega
          · intro tested
            rfl
          · intro tested
            rfl
      | cons next rest =>
          obtain ⟨initialInterior, envelopeDerivation,
              envelopePermutation⟩ :=
            existsExactEnvelopeOfConnected connected (by simp)
          let reduced :=
            endpointThresholdReduce head initialInterior
          let target := envelopeRender head reduced []
          have reduceDerivation :=
            listDerivesNormalizeInterior head initialInterior
          have combined : ListDerives (head :: next :: rest) target := by
            exact envelopeDerivation.trans <| by
              simpa [target, reduced] using reduceDerivation
          refine ⟨target, ?_⟩
          refine
            { derives := combined
              bounded := ?_
              capped := ?_
              parity := ?_
              shape := Or.inr ⟨head, reduced, rfl⟩ }
          · intro tested
            change (envelopeRender head reduced []).count tested ≤ 3
            rw [count_envelopeRender]
            exact endpointThresholdReduce_total_le_three
              head tested initialInterior
          · intro tested
            have sourceCount :=
              (List.perm_iff_count.mp envelopePermutation) tested
            have reducedCapped :=
              endpointThresholdReduce_total_capped
                head tested initialInterior
            change min ((envelopeRender head reduced []).count tested) 2 =
              min ((head :: next :: rest).count tested) 2
            rw [count_envelopeRender]
            rw [count_envelopeRender] at sourceCount
            exact reducedCapped.trans <| congrArg (fun count => min count 2)
              sourceCount.symm
          · intro tested
            have sourceCount :=
              (List.perm_iff_count.mp envelopePermutation) tested
            have reducedParity :=
              endpointThresholdReduce_total_mod_two
                head tested initialInterior
            change (envelopeRender head reduced []).count tested % 2 =
              (head :: next :: rest).count tested % 2
            rw [count_envelopeRender]
            rw [count_envelopeRender] at sourceCount
            exact reducedParity.trans <| congrArg (fun count => count % 2)
              sourceCount.symm

private theorem interior_perm_of_envelope_perm
    (endpoint : Nat) {left right : List Nat}
    (permutation :
      (envelopeRender endpoint left []).Perm
        (envelopeRender endpoint right [])) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro tested
  have counts := (List.perm_iff_count.mp permutation) tested
  simp only [envelopeRender, List.count_cons,
    List.count_append] at counts
  omega

private theorem existsEnvelopeRetarget
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (newCount : 2 ≤ interior.count newEndpoint) :
    ∃ targetInterior,
      ListDerives
        (envelopeRender oldEndpoint interior [])
        (envelopeRender newEndpoint targetInterior []) ∧
      (envelopeRender oldEndpoint interior []).Perm
        (envelopeRender newEndpoint targetInterior []) := by
  have firstMember : newEndpoint ∈ interior :=
    List.count_pos_iff.mp (by omega)
  have countAfterFirst :
      (interior.erase newEndpoint).count newEndpoint =
        interior.count newEndpoint - 1 := by
    rw [List.count_erase_self]
  have secondMember : newEndpoint ∈ interior.erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing := (interior.erase newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm (newEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase firstMember).trans <|
      List.Perm.cons newEndpoint <| by
        simpa [trailing] using List.perm_cons_erase secondMember
  have arrangeSource :=
    listDerivesInteriorPermutation oldEndpoint [] arrange
  have switch :=
    listDerivesEnvelopeSwitch oldEndpoint newEndpoint trailing
  let targetInterior := oldEndpoint :: oldEndpoint :: trailing
  have wholePermutation :
      (envelopeRender oldEndpoint interior []).Perm
        (envelopeRender newEndpoint targetInterior []) := by
    rw [List.perm_iff_count]
    intro tested
    have arrangeCount := (List.perm_iff_count.mp arrange) tested
    simp only [envelopeRender, targetInterior, List.count_cons,
      List.count_append] at arrangeCount ⊢
    omega
  exact
    ⟨targetInterior,
      arrangeSource.trans <| by
        simpa [targetInterior, envelopeRender, List.append_assoc] using switch,
      wholePermutation⟩

/-- Equal capped multiplicities and parity determine a derivation between
support-connected components. -/
private theorem listDerivesConnectedComponents
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (sameCapped : ∀ tested,
      min (left.count tested) 2 = min (right.count tested) 2)
    (sameParity : ∀ tested,
      left.count tested % 2 = right.count tested % 2) :
    ListDerives left right := by
  obtain ⟨leftTarget, leftNormal⟩ :=
    existsComponentNormal leftNonempty leftConnected
  obtain ⟨rightTarget, rightNormal⟩ :=
    existsComponentNormal rightNonempty rightConnected
  have targetCounts : ∀ tested,
      leftTarget.count tested = rightTarget.count tested := by
    intro tested
    have leftBound := leftNormal.bounded tested
    have rightBound := rightNormal.bounded tested
    have capped :
        min (leftTarget.count tested) 2 =
          min (rightTarget.count tested) 2 :=
      (leftNormal.capped tested).trans <|
        (sameCapped tested).trans (rightNormal.capped tested).symm
    have parity :
        leftTarget.count tested % 2 =
          rightTarget.count tested % 2 :=
      (leftNormal.parity tested).trans <|
        (sameParity tested).trans (rightNormal.parity tested).symm
    omega
  have targetsPerm : leftTarget.Perm rightTarget := by
    rw [List.perm_iff_count]
    exact targetCounts
  by_cases leftSingleton : leftTarget.length = 1
  · obtain ⟨letter, leftTargetEq⟩ :=
      List.length_eq_one_iff.mp leftSingleton
    have rightTargetEq : rightTarget = [letter] :=
      List.perm_singleton.mp <| by
        simpa [leftTargetEq] using targetsPerm.symm
    rw [leftTargetEq] at leftNormal
    rw [rightTargetEq] at rightNormal
    exact leftNormal.derives.trans rightNormal.derives.symm
  · rcases leftNormal.shape with leftLength | leftEnvelope
    · exact False.elim (leftSingleton leftLength)
    · obtain ⟨oldEndpoint, leftInterior, leftTargetEq⟩ := leftEnvelope
      rcases rightNormal.shape with rightLength | rightEnvelope
      · have lengths := targetsPerm.length_eq
        rw [leftTargetEq, rightLength] at lengths
        simp [envelopeRender] at lengths
      · obtain ⟨newEndpoint, rightInterior, rightTargetEq⟩ :=
          rightEnvelope
        rw [leftTargetEq] at leftNormal targetsPerm
        rw [rightTargetEq] at rightNormal targetsPerm
        by_cases sameEndpoint : oldEndpoint = newEndpoint
        · subst newEndpoint
          have interiorPerm :=
            interior_perm_of_envelope_perm oldEndpoint targetsPerm
          have middle :=
            listDerivesInteriorPermutation oldEndpoint [] interiorPerm
          exact leftNormal.derives.trans <|
            middle.trans rightNormal.derives.symm
        · have newInteriorCount : 2 ≤ leftInterior.count newEndpoint := by
            have counts :=
              (List.perm_iff_count.mp targetsPerm) newEndpoint
            simp only [envelopeRender, List.count_cons,
              List.count_append] at counts
            simp [sameEndpoint, Ne.symm sameEndpoint] at counts
            omega
          obtain ⟨switchedInterior, retarget, retargetPerm⟩ :=
            existsEnvelopeRetarget sameEndpoint newInteriorCount
          have switchedPerm :
              (envelopeRender newEndpoint switchedInterior []).Perm
                (envelopeRender newEndpoint rightInterior []) :=
            retargetPerm.symm.trans targetsPerm
          have interiorPerm :=
            interior_perm_of_envelope_perm newEndpoint switchedPerm
          have finish :=
            listDerivesInteriorPermutation newEndpoint [] interiorPerm
          exact leftNormal.derives.trans <|
            retarget.trans <| finish.trans rightNormal.derives.symm

/-! ## Ordered connected-component alignment -/

private theorem componentSignature_mem_of_mem
    {component : List Nat} {tested : Nat}
    (member : tested ∈ component) :
    tested ∈ (connectedComponentSignatureOfList component).support := by
  rw [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff]
  exact member

private theorem component_mem_of_signature_mem
    {component : List Nat} {tested : Nat}
    (member :
      tested ∈ (connectedComponentSignatureOfList component).support) :
    tested ∈ component := by
  rwa [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff] at member

private theorem flatten_mem_of_componentSignatures_eq
    {left right : List (List Nat)} {tested : Nat}
    (same :
      left.map connectedComponentSignatureOfList =
        right.map connectedComponentSignatureOfList)
    (member : tested ∈ left.flatten) :
    tested ∈ right.flatten := by
  rcases List.mem_flatten.mp member with
    ⟨component, componentMember, testedMember⟩
  have signatureMember :
      connectedComponentSignatureOfList component ∈
        right.map connectedComponentSignatureOfList := by
    rw [← same]
    exact List.mem_map.mpr ⟨component, componentMember, rfl⟩
  rcases List.mem_map.mp signatureMember with
    ⟨target, targetMember, signatureEq⟩
  apply List.mem_flatten_of_mem targetMember
  apply component_mem_of_signature_mem
  rw [signatureEq]
  exact componentSignature_mem_of_mem testedMember

private theorem flatten_mem_iff_of_componentSignatures_eq
    {left right : List (List Nat)}
    (same :
      left.map connectedComponentSignatureOfList =
        right.map connectedComponentSignatureOfList)
    (tested : Nat) :
    tested ∈ left.flatten ↔ tested ∈ right.flatten :=
  ⟨fun member =>
      flatten_mem_of_componentSignatures_eq same member,
    fun member =>
      flatten_mem_of_componentSignatures_eq same.symm member⟩

private theorem count_flatten_eq_component
    {components : List (List Nat)} {component : List Nat}
    {tested : Nat}
    (pairwise :
      components.Pairwise ConnectedComponentSupportsDisjoint)
    (componentMember : component ∈ components)
    (testedMember : tested ∈ component) :
    components.flatten.count tested = component.count tested := by
  induction components with
  | nil =>
      simp at componentMember
  | cons current remaining ih =>
      rw [List.pairwise_cons] at pairwise
      rcases List.mem_cons.mp componentMember with rfl | componentMember
      · have remainingAbsent : tested ∉ remaining.flatten := by
          intro remainingMember
          rcases List.mem_flatten.mp remainingMember with
            ⟨candidate, candidateMember, candidateContains⟩
          exact
            (pairwise.1 candidate candidateMember tested testedMember)
              candidateContains
        simp [List.count_eq_zero.mpr remainingAbsent]
      · have currentAbsent : tested ∉ current := by
          intro currentMember
          exact
            (pairwise.1 component componentMember tested currentMember)
              testedMember
        rw [List.flatten_cons, List.count_append,
          List.count_eq_zero.mpr currentAbsent,
          ih pairwise.2 componentMember]
        simp

private theorem head_disjoint_flatten
    {head : List Nat} {tail : List (List Nat)}
    (disjoint :
      ∀ component, component ∈ tail →
        ConnectedComponentSupportsDisjoint head component) :
    ConnectedComponentSupportsDisjoint head tail.flatten := by
  intro tested headMember tailMember
  rcases List.mem_flatten.mp tailMember with
    ⟨component, componentMember, componentContains⟩
  exact
    (disjoint component componentMember tested headMember)
      componentContains

private theorem listDerivesAlignedComponents :
    ∀ (leftComponents rightComponents : List (List Nat)),
      (∀ component, component ∈ leftComponents → component ≠ []) →
      (∀ component, component ∈ rightComponents → component ≠ []) →
      leftComponents.Pairwise ConnectedComponentSupportsDisjoint →
      rightComponents.Pairwise ConnectedComponentSupportsDisjoint →
      (∀ component, component ∈ leftComponents →
        ConnectedComponentSupportConnected component) →
      (∀ component, component ∈ rightComponents →
        ConnectedComponentSupportConnected component) →
      leftComponents.map connectedComponentSignatureOfList =
        rightComponents.map connectedComponentSignatureOfList →
      (∀ tested,
        min (leftComponents.flatten.count tested) 2 =
          min (rightComponents.flatten.count tested) 2) →
      (∀ tested,
        leftComponents.flatten.count tested % 2 =
          rightComponents.flatten.count tested % 2) →
      ListDerives leftComponents.flatten rightComponents.flatten
  | [], rightComponents, _, _, _, _, _, _, signaturesEqual, _, _ => by
      cases rightComponents with
      | nil => exact S5_107.ListDerives.empty
      | cons rightHead rightTail =>
          simp at signaturesEqual
  | leftHead :: leftTail, rightComponents,
      leftNonempty, rightNonempty,
      leftPairwise, rightPairwise,
      leftConnected, rightConnected,
      signaturesEqual, wholeCapped, wholeParity => by
      cases rightComponents with
      | nil =>
          simp at signaturesEqual
      | cons rightHead rightTail =>
          have leftPairwiseAll := leftPairwise
          have rightPairwiseAll := rightPairwise
          rw [List.pairwise_cons] at leftPairwise rightPairwise
          simp only [List.map_cons, List.cons.injEq] at signaturesEqual
          have headCapped : ∀ tested,
              min (leftHead.count tested) 2 =
                min (rightHead.count tested) 2 := by
            intro tested
            by_cases leftMember : tested ∈ leftHead
            · have leftSupport :=
                componentSignature_mem_of_mem leftMember
              have rightSupport :
                  tested ∈
                    (connectedComponentSignatureOfList rightHead).support := by
                rw [← signaturesEqual.1]
                exact leftSupport
              have rightMember :=
                component_mem_of_signature_mem rightSupport
              have leftWholeCount :=
                count_flatten_eq_component
                  leftPairwiseAll (by simp) leftMember
              have rightWholeCount :=
                count_flatten_eq_component
                  rightPairwiseAll (by simp) rightMember
              rw [← leftWholeCount, ← rightWholeCount]
              exact wholeCapped tested
            · have rightAbsent : tested ∉ rightHead := by
                intro rightMember
                have rightSupport :=
                  componentSignature_mem_of_mem rightMember
                have leftSupport :
                    tested ∈
                      (connectedComponentSignatureOfList leftHead).support := by
                  rw [signaturesEqual.1]
                  exact rightSupport
                exact leftMember <|
                  component_mem_of_signature_mem leftSupport
              rw [List.count_eq_zero.mpr leftMember,
                List.count_eq_zero.mpr rightAbsent]
          have headParity : ∀ tested,
              leftHead.count tested % 2 =
                rightHead.count tested % 2 := by
            intro tested
            by_cases leftMember : tested ∈ leftHead
            · have leftSupport :=
                componentSignature_mem_of_mem leftMember
              have rightSupport :
                  tested ∈
                    (connectedComponentSignatureOfList rightHead).support := by
                rw [← signaturesEqual.1]
                exact leftSupport
              have rightMember :=
                component_mem_of_signature_mem rightSupport
              have leftWholeCount :=
                count_flatten_eq_component
                  leftPairwiseAll (by simp) leftMember
              have rightWholeCount :=
                count_flatten_eq_component
                  rightPairwiseAll (by simp) rightMember
              rw [← leftWholeCount, ← rightWholeCount]
              exact wholeParity tested
            · have rightAbsent : tested ∉ rightHead := by
                intro rightMember
                have rightSupport :=
                  componentSignature_mem_of_mem rightMember
                have leftSupport :
                    tested ∈
                      (connectedComponentSignatureOfList leftHead).support := by
                  rw [signaturesEqual.1]
                  exact rightSupport
                exact leftMember <|
                  component_mem_of_signature_mem leftSupport
              rw [List.count_eq_zero.mpr leftMember,
                List.count_eq_zero.mpr rightAbsent]
          have headDerivation : ListDerives leftHead rightHead :=
            listDerivesConnectedComponents
              (leftNonempty leftHead (by simp))
              (rightNonempty rightHead (by simp))
              (leftConnected leftHead (by simp))
              (rightConnected rightHead (by simp))
              headCapped headParity
          have tailCapped : ∀ tested,
              min (leftTail.flatten.count tested) 2 =
                min (rightTail.flatten.count tested) 2 := by
            intro tested
            by_cases leftTailMember : tested ∈ leftTail.flatten
            · have rightTailMember : tested ∈ rightTail.flatten :=
                (flatten_mem_iff_of_componentSignatures_eq
                  signaturesEqual.2 tested).1 leftTailMember
              have leftHeadAbsent : tested ∉ leftHead := by
                intro leftHeadMember
                exact
                  (head_disjoint_flatten leftPairwise.1
                    tested leftHeadMember) leftTailMember
              have rightHeadAbsent : tested ∉ rightHead := by
                intro rightHeadMember
                exact
                  (head_disjoint_flatten rightPairwise.1
                    tested rightHeadMember) rightTailMember
              have counts := wholeCapped tested
              simp only [List.flatten_cons, List.count_append] at counts
              rw [List.count_eq_zero.mpr leftHeadAbsent,
                List.count_eq_zero.mpr rightHeadAbsent] at counts
              simpa using counts
            · have rightTailAbsent : tested ∉ rightTail.flatten := by
                intro rightTailMember
                exact leftTailMember <|
                  (flatten_mem_iff_of_componentSignatures_eq
                    signaturesEqual.2 tested).2 rightTailMember
              rw [List.count_eq_zero.mpr leftTailMember,
                List.count_eq_zero.mpr rightTailAbsent]
          have tailParity : ∀ tested,
              leftTail.flatten.count tested % 2 =
                rightTail.flatten.count tested % 2 := by
            intro tested
            by_cases leftTailMember : tested ∈ leftTail.flatten
            · have rightTailMember : tested ∈ rightTail.flatten :=
                (flatten_mem_iff_of_componentSignatures_eq
                  signaturesEqual.2 tested).1 leftTailMember
              have leftHeadAbsent : tested ∉ leftHead := by
                intro leftHeadMember
                exact
                  (head_disjoint_flatten leftPairwise.1
                    tested leftHeadMember) leftTailMember
              have rightHeadAbsent : tested ∉ rightHead := by
                intro rightHeadMember
                exact
                  (head_disjoint_flatten rightPairwise.1
                    tested rightHeadMember) rightTailMember
              have counts := wholeParity tested
              simp only [List.flatten_cons, List.count_append] at counts
              rw [List.count_eq_zero.mpr leftHeadAbsent,
                List.count_eq_zero.mpr rightHeadAbsent] at counts
              simpa using counts
            · have rightTailAbsent : tested ∉ rightTail.flatten := by
                intro rightTailMember
                exact leftTailMember <|
                  (flatten_mem_iff_of_componentSignatures_eq
                    signaturesEqual.2 tested).2 rightTailMember
              rw [List.count_eq_zero.mpr leftTailMember,
                List.count_eq_zero.mpr rightTailAbsent]
          have tailDerivation :=
            listDerivesAlignedComponents
              leftTail rightTail
              (fun component member =>
                leftNonempty component (by simp [member]))
              (fun component member =>
                rightNonempty component (by simp [member]))
              leftPairwise.2 rightPairwise.2
              (fun component member =>
                leftConnected component (by simp [member]))
              (fun component member =>
                rightConnected component (by simp [member]))
              signaturesEqual.2 tailCapped tailParity
          have first := headDerivation.append leftTail.flatten
          have second := tailDerivation.prepend rightHead
          simpa [List.append_assoc] using first.trans second

/-- The combined `S5_379` signature and cyclic-two parity signature are
sufficient for a derivation from the four Condition 7 laws. -/
private theorem derives_of_sameSignature_and_parity
    {left right : Word Nat}
    (same : S5_379.SameComponentSimpleSignature left right)
    (sameParity : ∀ tested,
      left.toList.count tested % 2 = right.toList.count tested % 2) :
    Derives B left right := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signaturesEqual :
      leftComponents.map connectedComponentSignatureOfList =
        rightComponents.map connectedComponentSignatureOfList := by
    simpa [leftComponents, rightComponents,
      connectedComponentSignaturesWord,
      connectedComponentSignaturesList,
      connectedComponentDecomposeWord] using
        S5_379.sameComponentSignatures_of_sameComponentSimpleSignature same
  have leftFlatten : leftComponents.flatten = left.toList := by
    simpa [leftComponents] using
      connectedComponentDecomposeWord_flatten left
  have rightFlatten : rightComponents.flatten = right.toList := by
    simpa [rightComponents] using
      connectedComponentDecomposeWord_flatten right
  have flattenedCapped : ∀ tested,
      min (leftComponents.flatten.count tested) 2 =
        min (rightComponents.flatten.count tested) 2 := by
    intro tested
    rw [leftFlatten, rightFlatten]
    exact S5_379.cappedCounts_eq_of_sameComponentSimpleSignature
      same tested
  have flattenedParity : ∀ tested,
      leftComponents.flatten.count tested % 2 =
        rightComponents.flatten.count tested % 2 := by
    intro tested
    rw [leftFlatten, rightFlatten]
    exact sameParity tested
  have componentDerivation :=
    listDerivesAlignedComponents
      leftComponents rightComponents
      (connectedComponentDecomposeWord_nonempty_components left)
      (connectedComponentDecomposeWord_nonempty_components right)
      (connectedComponentDecomposeWord_pairwiseDisjoint left)
      (connectedComponentDecomposeWord_pairwiseDisjoint right)
      (connectedComponentDecomposeWord_supportConnected left)
      (connectedComponentDecomposeWord_supportConnected right)
      signaturesEqual flattenedCapped flattenedParity
  have listDerivation : ListDerives left.toList right.toList := by
    change
      ListDerives
        (connectedComponentDecomposeWord left).flatten
        (connectedComponentDecomposeWord right).flatten
      at componentDerivation
    rw [connectedComponentDecomposeWord_flatten left,
      connectedComponentDecomposeWord_flatten right]
      at componentDerivation
    exact componentDerivation
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact S5_107.ListDerives.toWord listDerivation

/-- Unconditional unrestricted completeness for Lee--Zhang Condition 7. -/
theorem complete : Condition7.DerivationalObligation := by
  intro identity cyclicValid coreValid
  have coreValid' :
      identity.SatisfiedBy S5_379.table.semigroup := by
    simpa [Condition7.core, Condition7.coreTable] using coreValid
  have cyclicValid' :
      identity.SatisfiedBy cyclicTwo.semigroup := by
    simpa [Condition7.cyclic, Condition7.cyclicTable,
      SemigroupBasis.Generated.S2_2.table_eq_catalogue_model] using
        cyclicValid
  exact derives_of_sameSignature_and_parity
    (S5_379.valid_sameSignature identity coreValid')
    (cyclicValid_parity_eq identity cyclicValid')

end SemigroupBasis.CoRoots.Order6LeeZhangCondition7Completeness

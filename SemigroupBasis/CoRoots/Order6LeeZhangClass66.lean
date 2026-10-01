import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_254Family
import SemigroupBasis.Generated.S2_4
import SemigroupBasis.Subdirect

/-!
# Lee--Zhang class 66

This file formalizes the four identities defining Lee--Zhang's variety
`X(7.1)` and proves that they axiomatize the intersection of the identity
theory of the two-element left-zero semigroup with the identity theory of
Edmunds' monoid `M18` (`S5_254`).  The proof follows Lemmas 7.2 and 7.5 and
Proposition 7.4 of Lee--Zhang.

The existing `S5_254` completeness theorem supplies the canonical
combinatorics.  Its derivations are replayed below one fixed nonempty prefix;
under such a prefix all fifteen M18 axioms follow from the four displayed
laws.  A simple common head is then peeled off using the identity element of
S5_254.  A repeated common head is handled by the fresh-prefix argument of
Lemma 7.5.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangClass66

open SemigroupBasis

private abbrev ListDerives :=
  SemigroupBasis.CoRoots.S5_107.ListDerives

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

@[simp]
private theorem w_toList (head : Nat) (tail : List Nat) :
    (w head tail).toList = head :: tail := by
  rfl

def xx : Word Nat := w 0 [0]
def xxxx : Word Nat := w 0 [0, 0, 0]
def xxxyx : Word Nat := w 0 [0, 0, 1, 0]
def xyx : Word Nat := w 0 [1, 0]
def xyxy : Word Nat := w 0 [1, 0, 1]
def xxyy : Word Nat := w 0 [0, 1, 1]
def xyyz : Word Nat := w 0 [1, 1, 2]
def xzyy : Word Nat := w 0 [2, 1, 1]

def powerLaw : Identity Nat := ⟨xxxx, xx⟩
def sandwichLaw : Identity Nat := ⟨xxxyx, xyx⟩
def alternatingLaw : Identity Nat := ⟨xyxy, xxyy⟩
def squareTransportLaw : Identity Nat := ⟨xyyz, xzyy⟩

/-- Lee--Zhang (7.1), with the two members of `x^3 H x = x H x`
made explicit. -/
def basis : List (Identity Nat) :=
  [powerLaw, sandwichLaw, alternatingLaw, squareTransportLaw]

private def instantiateThreeWords
    (u v z : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem bind_append
    (u v : Word Nat) (sigma : Nat → Word Nat) :
    (u ++ v).bind sigma = u.bind sigma ++ v.bind sigma := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind
    (word : Word Nat) (tau sigma : Nat → Word Nat) :
    (word.bind tau).bind sigma =
      word.bind (fun letter => (tau letter).bind sigma) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem basisPower : Derives basis xxxx xx :=
  Derives.fromBasis (e := powerLaw) (by simp [basis])

private theorem basisSandwich : Derives basis xxxyx xyx :=
  Derives.fromBasis (e := sandwichLaw) (by simp [basis])

private theorem basisAlternating : Derives basis xyxy xxyy :=
  Derives.fromBasis (e := alternatingLaw) (by simp [basis])

private theorem basisSquareTransport : Derives basis xyyz xzyy :=
  Derives.fromBasis (e := squareTransportLaw) (by simp [basis])

/-- Lee--Zhang (7.2a), first member. -/
theorem derivesFourToTwo (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) (u ++ u) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords u u u)
  simpa [powerLaw, xxxx, xx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Lee--Zhang (7.2a), second member. -/
theorem derivesLeftSandwich (u middle : Word Nat) :
    Derives basis ((((u ++ u) ++ u) ++ middle) ++ u)
      ((u ++ middle) ++ u) := by
  have substituted :=
    Derives.subst basisSandwich
      (instantiateThreeWords u middle middle)
  simpa [sandwichLaw, xxxyx, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

theorem derivesAlternatingSquares (u v : Word Nat) :
    Derives basis (((u ++ v) ++ u) ++ v)
      ((u ++ u) ++ (v ++ v)) := by
  have substituted :=
    Derives.subst basisAlternating (instantiateThreeWords u v v)
  simpa [alternatingLaw, xyxy, xxyy, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Move a square across an arbitrary nonempty block after a fixed prefix. -/
theorem derivesSquareTransport (pre square block : Word Nat) :
    Derives basis ((pre ++ (square ++ square)) ++ block)
      ((pre ++ block) ++ (square ++ square)) := by
  have substituted :=
    Derives.subst basisSquareTransport
      (instantiateThreeWords pre square block)
  simpa [squareTransportLaw, xyyz, xzyy, w,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Lee--Zhang (7.2a), third member. -/
theorem derivesRightSandwich (u middle : Word Nat) :
    Derives basis ((((u ++ middle) ++ u) ++ u) ++ u)
      ((u ++ middle) ++ u) := by
  have moved :=
    Derives.appendRight (derivesSquareTransport u u middle) u
  have contracted := derivesLeftSandwich u middle
  have moved' :
      Derives basis ((((u ++ middle) ++ u) ++ u) ++ u)
        ((((u ++ u) ++ u) ++ middle) ++ u) := by
    simpa [Word.append_assoc] using moved.symm
  have contracted' :
      Derives basis ((((u ++ u) ++ u) ++ middle) ++ u)
        ((u ++ middle) ++ u) := by
    simpa [Word.append_assoc] using contracted
  exact moved'.trans contracted'

private theorem derives_of_listDerives_toList
    {left right : Word Nat}
    (derivation : ListDerives basis left.toList right.toList) :
    Derives basis left right := by
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.toList] using
              SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation

private def extendWord (first : Word Nat) (rest : List Nat) : Word Nat :=
  ⟨first.head, first.tail ++ rest⟩

@[simp]
private theorem extendWord_toList (first : Word Nat) (rest : List Nat) :
    (extendWord first rest).toList = first.toList ++ rest := by
  simp [extendWord, Word.toList]

/-- The nonempty word rendered by an optional prefix, one mandatory word,
and an optional suffix. -/
private def contextWord
    (before : List Nat) (middle : Word Nat) (after : List Nat) : Word Nat :=
  match before with
  | [] => extendWord middle after
  | head :: tail => ⟨head, tail ++ middle.toList ++ after⟩

@[simp]
private theorem contextWord_toList
    (before : List Nat) (middle : Word Nat) (after : List Nat) :
    (contextWord before middle after).toList =
      before ++ middle.toList ++ after := by
  cases before <;>
    simp [contextWord, extendWord, Word.toList, List.append_assoc]

/-- Insert two copies of `letter` beside its first displayed occurrence.
The second displayed occurrence witnesses the sandwich contraction; when the
gap is empty the unary fourth-power law is used instead. -/
private theorem listDerivesInsertPairAfterFirst
    (letter : Word Nat) (between suffix : List Nat) :
    ListDerives basis
      (letter.toList ++ between ++ letter.toList ++ suffix)
      (letter.toList ++ letter.toList ++ letter.toList ++ between ++
        letter.toList ++ suffix) := by
  cases between with
  | nil =>
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesFourToTwo letter).symm
      simpa [List.append_assoc] using
        expanded.append suffix
  | cons head tail =>
      let middle : Word Nat := ⟨head, tail⟩
      have expanded :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesLeftSandwich letter middle).symm
      simpa [middle, Word.toList, List.append_assoc] using
        expanded.append suffix

/-- Move the inserted square through the gap, so it lies beside the second
displayed occurrence. -/
private theorem listDerivesInsertPairAfterSecond
    (letter : Word Nat) (between suffix : List Nat) :
    ListDerives basis
      (letter.toList ++ between ++ letter.toList ++ suffix)
      (letter.toList ++ between ++ letter.toList ++ letter.toList ++
        letter.toList ++ suffix) := by
  have inserted :=
    listDerivesInsertPairAfterFirst letter between suffix
  cases between with
  | nil =>
      simpa [List.append_assoc] using inserted
  | cons head tail =>
      let middle : Word Nat := ⟨head, tail⟩
      have moved :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesSquareTransport letter letter middle)
      have contextual := moved.append (letter.toList ++ suffix)
      exact inserted.trans <| by
        simpa [middle, Word.toList, List.append_assoc] using contextual

/-!
## Lee--Zhang (7.2d)

The next three list-level lemmas are the three witnessed adjacent swaps in
(7.2d).  Raw lists represent the optional `H`, `K`, and `T` contexts, so the
same theorem covers every elimination allowed by the paper's sans-serif
letter convention.
-/

/-- `h x y K x T y = h y x K x T y`. -/
private theorem listDerivesSwapWithFutureWitnesses
    (h x y : Word Nat) (k t : List Nat) :
    ListDerives basis
      (h.toList ++ x.toList ++ y.toList ++ k ++ x.toList ++ t ++ y.toList)
      (h.toList ++ y.toList ++ x.toList ++ k ++ x.toList ++ t ++ y.toList) := by
  let middleY := extendWord x (k ++ x.toList ++ t)
  have expandYCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesLeftSandwich y middleY).symm
  have expandY : ListDerives basis
      (h.toList ++ y.toList ++ x.toList ++ k ++ x.toList ++ t ++ y.toList)
      (h.toList ++ y.toList ++ y.toList ++ y.toList ++ x.toList ++ k ++
        x.toList ++ t ++ y.toList) := by
    simpa [middleY, List.append_assoc] using
      expandYCore.prepend h.toList
  have expandX :=
    listDerivesInsertPairAfterFirst x k (t ++ y.toList)
  have expandBoth : ListDerives basis
      (h.toList ++ y.toList ++ y.toList ++ y.toList ++ x.toList ++ k ++
        x.toList ++ t ++ y.toList)
      (h.toList ++ y.toList ++ y.toList ++ y.toList ++ x.toList ++ x.toList ++
        x.toList ++ k ++ x.toList ++ t ++ y.toList) := by
    simpa [List.append_assoc] using
      expandX.prepend
        (h.toList ++ y.toList ++ y.toList ++ y.toList)
  let hy := h ++ y
  let xx := x ++ x
  have moveYAcrossXXCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesSquareTransport hy y xx)
  have moveYAcrossXX : ListDerives basis
      (h.toList ++ y.toList ++ y.toList ++ y.toList ++ x.toList ++ x.toList ++
        x.toList ++ k ++ x.toList ++ t ++ y.toList)
      (h.toList ++ y.toList ++ x.toList ++ x.toList ++ y.toList ++ y.toList ++
        x.toList ++ k ++ x.toList ++ t ++ y.toList) := by
    simpa [hy, xx, List.append_assoc] using
      moveYAcrossXXCore.append
        (x.toList ++ k ++ x.toList ++ t ++ y.toList)
  have moveXBeforeYCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesSquareTransport h x y).symm
  have moveXBeforeY : ListDerives basis
      (h.toList ++ y.toList ++ x.toList ++ x.toList ++ y.toList ++ y.toList ++
        x.toList ++ k ++ x.toList ++ t ++ y.toList)
      (h.toList ++ x.toList ++ x.toList ++ y.toList ++ y.toList ++ y.toList ++
        x.toList ++ k ++ x.toList ++ t ++ y.toList) := by
    simpa [List.append_assoc] using
      moveXBeforeYCore.append
        (y.toList ++ y.toList ++ x.toList ++ k ++ x.toList ++ t ++ y.toList)
  let hxxy := ((h ++ x) ++ x) ++ y
  have moveYPairAcrossXCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesSquareTransport hxxy y x)
  have moveYPairAcrossX : ListDerives basis
      (h.toList ++ x.toList ++ x.toList ++ y.toList ++ y.toList ++ y.toList ++
        x.toList ++ k ++ x.toList ++ t ++ y.toList)
      (h.toList ++ x.toList ++ x.toList ++ y.toList ++ x.toList ++ y.toList ++
        y.toList ++ k ++ x.toList ++ t ++ y.toList) := by
    simpa [hxxy, List.append_assoc] using
      moveYPairAcrossXCore.append
        (k ++ x.toList ++ t ++ y.toList)
  have collapseAlternatingCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesAlternatingSquares x y)
  have collapseAlternating : ListDerives basis
      (h.toList ++ x.toList ++ x.toList ++ y.toList ++ x.toList ++ y.toList ++
        y.toList ++ k ++ x.toList ++ t ++ y.toList)
      (h.toList ++ x.toList ++ x.toList ++ x.toList ++ y.toList ++ y.toList ++
        y.toList ++ k ++ x.toList ++ t ++ y.toList) := by
    simpa [List.append_assoc] using
      (collapseAlternatingCore.prepend (h.toList ++ x.toList)).append
        (y.toList ++ k ++ x.toList ++ t ++ y.toList)
  let middleX := extendWord y (y.toList ++ y.toList ++ k)
  have contractXCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesLeftSandwich x middleX)
  have contractX : ListDerives basis
      (h.toList ++ x.toList ++ x.toList ++ x.toList ++ y.toList ++ y.toList ++
        y.toList ++ k ++ x.toList ++ t ++ y.toList)
      (h.toList ++ x.toList ++ y.toList ++ y.toList ++ y.toList ++ k ++
        x.toList ++ t ++ y.toList) := by
    simpa [middleX, List.append_assoc] using
      (contractXCore.prepend h.toList).append (t ++ y.toList)
  let middleYFinal := contextWord k x t
  have contractYCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesLeftSandwich y middleYFinal)
  have contractY : ListDerives basis
      (h.toList ++ x.toList ++ y.toList ++ y.toList ++ y.toList ++ k ++
        x.toList ++ t ++ y.toList)
      (h.toList ++ x.toList ++ y.toList ++ k ++ x.toList ++ t ++ y.toList) := by
    simpa [middleYFinal, List.append_assoc] using
      contractYCore.prepend (h.toList ++ x.toList)
  exact (expandY.trans <| expandBoth.trans <|
    moveYAcrossXX.trans <| moveXBeforeY.trans <|
      moveYPairAcrossX.trans <| collapseAlternating.trans <|
        contractX.trans contractY).symm

/-- `x H x y K y = x H y x K y`. -/
private theorem listDerivesSwapWithPastAndFuture
    (x : Word Nat) (h : List Nat) (y : Word Nat) (k : List Nat) :
    ListDerives basis
      (x.toList ++ h ++ x.toList ++ y.toList ++ k ++ y.toList)
      (x.toList ++ h ++ y.toList ++ x.toList ++ k ++ y.toList) := by
  have insertAtSecond :=
    listDerivesInsertPairAfterSecond x h
      (y.toList ++ k ++ y.toList)
  let xhx := extendWord x (h ++ x.toList)
  let yk := extendWord y k
  have movePairRightCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesSquareTransport xhx x yk)
  have movePairRight : ListDerives basis
      (x.toList ++ h ++ x.toList ++ x.toList ++ x.toList ++ y.toList ++ k ++
        y.toList)
      (x.toList ++ h ++ x.toList ++ y.toList ++ k ++ x.toList ++ x.toList ++
        y.toList) := by
    simpa [xhx, yk, List.append_assoc] using
      movePairRightCore.append y.toList
  let xh := extendWord x h
  have swap :=
    listDerivesSwapWithFutureWitnesses xh x y k x.toList
  have swapped : ListDerives basis
      (x.toList ++ h ++ x.toList ++ y.toList ++ k ++ x.toList ++ x.toList ++
        y.toList)
      (x.toList ++ h ++ y.toList ++ x.toList ++ k ++ x.toList ++ x.toList ++
        y.toList) := by
    simpa [xh, List.append_assoc] using swap
  let hyxk := contextWord h y (x.toList ++ k)
  have movePairLeftCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesSquareTransport x x hyxk).symm
  have movePairLeft : ListDerives basis
      (x.toList ++ h ++ y.toList ++ x.toList ++ k ++ x.toList ++ x.toList ++
        y.toList)
      (x.toList ++ x.toList ++ x.toList ++ h ++ y.toList ++ x.toList ++ k ++
        y.toList) := by
    simpa [hyxk, List.append_assoc] using
      movePairLeftCore.append y.toList
  have removeAtFirst :=
    (listDerivesInsertPairAfterFirst x (h ++ y.toList)
      (k ++ y.toList)).symm
  have removed : ListDerives basis
      (x.toList ++ x.toList ++ x.toList ++ h ++ y.toList ++ x.toList ++ k ++
        y.toList)
      (x.toList ++ h ++ y.toList ++ x.toList ++ k ++ y.toList) := by
    simpa [List.append_assoc] using removeAtFirst
  have inserted : ListDerives basis
      (x.toList ++ h ++ x.toList ++ y.toList ++ k ++ y.toList)
      (x.toList ++ h ++ x.toList ++ x.toList ++ x.toList ++ y.toList ++ k ++
        y.toList) := by
    simpa [List.append_assoc] using insertAtSecond
  exact inserted.trans <| movePairRight.trans <|
    swapped.trans <| movePairLeft.trans removed

/-- `x H y K x y = x H y K y x`. -/
private theorem listDerivesSwapWithPastWitnesses
    (x : Word Nat) (h : List Nat) (y : Word Nat) (k : List Nat) :
    ListDerives basis
      (x.toList ++ h ++ y.toList ++ k ++ x.toList ++ y.toList)
      (x.toList ++ h ++ y.toList ++ k ++ y.toList ++ x.toList) := by
  have insertY :=
    listDerivesInsertPairAfterFirst y (k ++ x.toList) []
  have expanded : ListDerives basis
      (x.toList ++ h ++ y.toList ++ k ++ x.toList ++ y.toList)
      (x.toList ++ h ++ y.toList ++ y.toList ++ y.toList ++ k ++ x.toList ++
        y.toList) := by
    simpa [List.append_assoc] using insertY.prepend (x.toList ++ h)
  let xhy := extendWord x (h ++ y.toList)
  let kx := contextWord k x []
  have moveYRightCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesSquareTransport xhy y kx)
  have moveYRight : ListDerives basis
      (x.toList ++ h ++ y.toList ++ y.toList ++ y.toList ++ k ++ x.toList ++
        y.toList)
      (x.toList ++ h ++ y.toList ++ k ++ x.toList ++ y.toList ++ y.toList ++
        y.toList) := by
    simpa [xhy, kx, List.append_assoc] using
      moveYRightCore.append y.toList
  have swap :=
    listDerivesSwapWithPastAndFuture x
      (h ++ y.toList ++ k) y y.toList
  have swapped : ListDerives basis
      (x.toList ++ h ++ y.toList ++ k ++ x.toList ++ y.toList ++ y.toList ++
        y.toList)
      (x.toList ++ h ++ y.toList ++ k ++ y.toList ++ x.toList ++ y.toList ++
        y.toList) := by
    simpa [List.append_assoc] using swap
  let xhyPrefix := extendWord x (h ++ y.toList)
  let kyx := contextWord k y x.toList
  have moveYLeftCore :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesSquareTransport xhyPrefix y kyx).symm
  have moveYLeft : ListDerives basis
      (x.toList ++ h ++ y.toList ++ k ++ y.toList ++ x.toList ++ y.toList ++
        y.toList)
      (x.toList ++ h ++ y.toList ++ y.toList ++ y.toList ++ k ++ y.toList ++
        x.toList) := by
    simpa [xhyPrefix, kyx, List.append_assoc] using
      moveYLeftCore
  have removeY :=
    (listDerivesInsertPairAfterFirst y k x.toList).symm
  have removed : ListDerives basis
      (x.toList ++ h ++ y.toList ++ y.toList ++ y.toList ++ k ++ y.toList ++
        x.toList)
      (x.toList ++ h ++ y.toList ++ k ++ y.toList ++ x.toList) := by
    simpa [List.append_assoc] using
      removeY.prepend (x.toList ++ h)
  exact expanded.trans <| moveYRight.trans <|
    swapped.trans <| moveYLeft.trans removed

/-! ## Protected replay of the M18 basis -/

private theorem m18Basis_eq_explicit : S5_254.basis =
    [⟨w 0 [0], w 0 [0, 0, 0]⟩,
     ⟨w 0 [0, 0, 1, 0], w 0 [1, 0]⟩,
     ⟨w 0 [0, 1], w 1 [0, 0]⟩,
     ⟨w 0 [0, 2, 3, 2], w 0 [2, 0, 3, 2]⟩,
     ⟨w 0 [0, 2, 2], w 0 [2, 0, 2]⟩,
     ⟨w 0 [1, 0, 3, 1], w 1 [0, 0, 3, 1]⟩,
     ⟨w 0 [1, 0, 1], w 1 [0, 0, 1]⟩,
     ⟨w 0 [1, 0, 2, 3, 2], w 0 [1, 2, 0, 3, 2]⟩,
     ⟨w 0 [1, 0, 2, 2], w 0 [1, 2, 0, 2]⟩,
     ⟨w 0 [1, 2, 3, 0, 2], w 0 [1, 2, 3, 2, 0]⟩,
     ⟨w 0 [1, 2, 0, 3, 1], w 1 [0, 2, 0, 3, 1]⟩,
     ⟨w 0 [1, 2, 0, 1], w 1 [0, 2, 0, 1]⟩,
     ⟨w 0 [1, 2, 0, 2], w 0 [1, 2, 2, 0]⟩,
     ⟨w 0 [2, 3, 0, 2], w 0 [2, 3, 2, 0]⟩,
     ⟨w 0 [2, 0, 2], w 0 [2, 2, 0]⟩] := by
  rfl

/-- Every M18 derivation can be replayed after one fixed nonempty prefix.
This is the formal reuse boundary between the existing M18 canonical proof
and Lee--Zhang Section 7. -/
theorem liftM18DerivationAfterPrefix
    {left right : Word Nat}
    (derivation : Derives S5_254.basis left right)
    (pre : Word Nat) (sigma : Nat → Word Nat) :
    Derives basis
      (pre ++ left.bind sigma)
      (pre ++ right.bind sigma) := by
  induction derivation generalizing pre sigma with
  | fromBasis member =>
      simp only [m18Basis_eq_explicit, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [w, S5_254.powerLaw, S5_254.xx, S5_254.xxxx,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend pre (derivesFourToTwo (sigma 0)).symm
      · simpa [w, S5_254.sandwichContractionLaw, S5_254.xxxyx, S5_254.xyx,
          Word.bind, Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend pre
            (derivesLeftSandwich (sigma 0) (sigma 1))
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.prefixRotationLaw, S5_254.xxy, S5_254.yxx,
          Word.toList_bind, List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesSquareTransport pre (sigma 0) (sigma 1)))
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.zwzPrefixLaw, S5_254.xxzwz, S5_254.xzxwz,
          Word.toList_bind, List.append_assoc] using
          (listDerivesSwapWithPastAndFuture
            (sigma 0) [] (sigma 2) (sigma 3).toList).prepend pre.toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.doubleZPrefixLaw, S5_254.xxzz, S5_254.xzxz,
          Word.toList_bind, List.append_assoc] using
          (listDerivesSwapWithPastAndFuture
            (sigma 0) [] (sigma 2) []).prepend pre.toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.wyRotationLaw, S5_254.xyxwy, S5_254.yxxwy,
          Word.toList_bind, List.append_assoc] using
          listDerivesSwapWithFutureWitnesses
            pre (sigma 0) (sigma 1) [] (sigma 3).toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.alternatingPairLaw, S5_254.xyxy, S5_254.yxxy,
          Word.toList_bind, List.append_assoc] using
          listDerivesSwapWithFutureWitnesses
            pre (sigma 0) (sigma 1) [] []
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.longZwzTransportLaw, S5_254.xyxzwz, S5_254.xyzxwz,
          Word.toList_bind, List.append_assoc] using
          (listDerivesSwapWithPastAndFuture
            (sigma 0) (sigma 1).toList (sigma 2)
              (sigma 3).toList).prepend pre.toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.doubleZTransportLaw, S5_254.xyxzz, S5_254.xyzxz,
          Word.toList_bind, List.append_assoc] using
          (listDerivesSwapWithPastAndFuture
            (sigma 0) (sigma 1).toList (sigma 2) []).prepend pre.toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.crossedWZLaw, S5_254.xyzwxz, S5_254.xyzwzx,
          Word.toList_bind, List.append_assoc] using
          (listDerivesSwapWithPastWitnesses
            (sigma 0) (sigma 1).toList (sigma 2)
              (sigma 3).toList).prepend pre.toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.wyPrefixTransportLaw, S5_254.xyzxwy, S5_254.yxzxwy,
          Word.toList_bind, List.append_assoc] using
          listDerivesSwapWithFutureWitnesses
            pre (sigma 0) (sigma 1) (sigma 2).toList
              (sigma 3).toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.terminalYTransportLaw, S5_254.xyzxy, S5_254.yxzxy,
          Word.toList_bind, List.append_assoc] using
          listDerivesSwapWithFutureWitnesses
            pre (sigma 0) (sigma 1) (sigma 2).toList []
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.terminalZTransportLaw, S5_254.xyzxz, S5_254.xyzzx,
          Word.toList_bind, List.append_assoc] using
          (listDerivesSwapWithPastWitnesses
            (sigma 0) (sigma 1).toList (sigma 2) []).prepend pre.toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.wzCrossingLaw, S5_254.xzwxz, S5_254.xzwzx,
          Word.toList_bind, List.append_assoc] using
          (listDerivesSwapWithPastWitnesses
            (sigma 0) [] (sigma 2) (sigma 3).toList).prepend pre.toList
      · apply derives_of_listDerives_toList
        simpa [w_toList, S5_254.alternatingZLaw, S5_254.xzxz, S5_254.xzzx,
          Word.toList_bind, List.append_assoc] using
          (listDerivesSwapWithPastWitnesses
            (sigma 0) [] (sigma 2) []).prepend pre.toList
  | refl =>
      exact Derives.refl _
  | symm _ induction =>
      exact (induction pre sigma).symm
  | trans _ _ first second =>
      exact (first pre sigma).trans (second pre sigma)
  | prepend added _ induction =>
      simpa [bind_append, Word.append_assoc] using
        induction (pre ++ added.bind sigma) sigma
  | appendRight _ suffix induction =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (induction pre sigma) (suffix.bind sigma)
  | subst _ tau induction =>
      simpa [bind_bind] using
        induction pre (fun letter => (tau letter).bind sigma)

/-! ## Finite soundness checks and the two M18 orientations -/

private def toFinFour : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

private def mappedBasis (source : List (Identity Nat)) :
    List (Identity (Fin 4)) :=
  source.map fun identity => identity.map toFinFour

private theorem modelsMappedBasis
    (source : List (Identity Nat)) (candidate : FiniteTable)
    (roundTrip : source.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true)
    (checked : (mappedBasis source).all candidate.checkIdentity = true) :
    Models candidate.semigroup source := by
  intro identity member
  have finiteMember : identity.map toFinFour ∈ mappedBasis source :=
    List.mem_map.mpr ⟨identity, member, rfl⟩
  have finiteValid :=
    candidate.checkIdentityNat_sound (identity.map toFinFour)
      ((List.all_eq_true.mp checked) _ finiteMember)
  have restored : (identity.map toFinFour).map Fin.val = identity :=
    of_decide_eq_true <|
      (List.all_eq_true.mp roundTrip) identity member
  rw [restored] at finiteValid
  exact finiteValid

private theorem basisRoundTrip :
    basis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

theorem modelsLeftZero :
    Models SemigroupBasis.Generated.S2_4.table.semigroup basis :=
  modelsMappedBasis basis SemigroupBasis.Generated.S2_4.table
    basisRoundTrip (by decide)

set_option maxHeartbeats 1000000 in
theorem modelsM18 : Models S5_254.table.semigroup basis :=
  modelsMappedBasis basis S5_254.table basisRoundTrip (by decide)

private theorem reversedBasisRoundTrip :
    (reversedBasis basis).all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

set_option maxHeartbeats 1000000 in
private theorem modelsReversedBasisOnM18 :
    Models S5_254.table.semigroup (reversedBasis basis) :=
  modelsMappedBasis (reversedBasis basis) S5_254.table
    reversedBasisRoundTrip (by decide)

theorem modelsM18Opposite : Models S5_254.table.semigroup.opposite basis := by
  intro identity member
  apply (identity.satisfiedBy_opposite_iff_reversed S5_254.table.semigroup).2
  exact modelsReversedBasisOnM18 identity.reversed
    (List.mem_map.mpr ⟨identity, member, rfl⟩)

private theorem m18OppositeBasisRoundTrip :
    S5_254.oppositeBasis.all (fun identity =>
      decide ((identity.map toFinFour).map Fin.val = identity)) = true := by
  decide

set_option maxHeartbeats 2000000 in
private theorem modelsM18OppositeBasisOnM18 :
    Models S5_254.table.semigroup S5_254.oppositeBasis :=
  modelsMappedBasis S5_254.oppositeBasis S5_254.table
    m18OppositeBasisRoundTrip (by decide)

/-- M18 and its opposite generate the same semigroup variety.  Only the
direction needed by the class-66 target with opposite quotient is exposed. -/
theorem m18Valid_of_oppositeValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy S5_254.table.semigroup.opposite) :
    identity.SatisfiedBy S5_254.table.semigroup := by
  have derivation := S5_254.oppositeBasisFor.2 identity valid
  intro valuation
  exact derivation.sound modelsM18OppositeBasisOnM18 valuation

/-! ## Head and tail semantics -/

@[simp]
private theorem generatedLeftZeroMul
    (a b : Fin 2) :
    SemigroupBasis.Generated.S2_4.table.semigroup.mul a b = a := by
  rfl

theorem generatedLeftZeroEval
    (valuation : Nat → Fin 2) (word : Word Nat) :
    SemigroupBasis.Generated.S2_4.table.semigroup.eval valuation word =
      valuation word.head := by
  cases word with
  | mk head tail =>
      induction tail with
      | nil => rfl
      | cons next rest induction =>
          simp only [Semigroup.eval, List.foldl_cons]
          rw [generatedLeftZeroMul]
          exact induction

private theorem heads_eq_of_leftZero_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemigroupBasis.Generated.S2_4.table.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 := fun letter =>
    if letter = identity.lhs.head then 0 else 1
  have evaluated := valid valuation
  rw [generatedLeftZeroEval, generatedLeftZeroEval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

@[simp]
private theorem m18LeftIdentity (value : Fin 5) :
    SemigroupBasis.Generated.Catalogue.S5_254.mul 3 value = value := by
  decide +revert

private def identityAtHead
    (head : Nat) (valuation : Nat → Fin 5) : Nat → Fin 5 :=
  fun letter => if letter = head then 3 else valuation letter

private theorem m18EvalList_cons_identity_of_absent
    (head : Nat) (letters : List Nat) (nonempty : letters ≠ [])
    (absent : head ∉ letters) (valuation : Nat → Fin 5) :
    S5_254.m18EvalList (identityAtHead head valuation) (head :: letters) =
      S5_254.m18EvalList valuation letters := by
  obtain ⟨next, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  have nextNe : next ≠ head := by
    intro equal
    apply absent
    simp [equal]
  have restAgree : ∀ letter, letter ∈ rest →
      identityAtHead head valuation letter = valuation letter := by
    intro letter member
    have different : letter ≠ head := by
      intro equal
      exact absent (equal ▸ List.Mem.tail next member)
    simp [identityAtHead, different]
  simp only [S5_254.m18EvalList, S5_254.m18EvalFrom_cons, S5_254.m18ListStep]
  simp only [identityAtHead, if_pos, if_neg nextNe, m18LeftIdentity]
  exact S5_254.m18EvalFrom_congr (.value (valuation next))
    (identityAtHead head valuation) valuation rest restAgree

private theorem tailIdentity_valid
    (head leftHead rightHead : Nat) (leftTail rightTail : List Nat)
    (leftAbsent : head ∉ leftHead :: leftTail)
    (rightAbsent : head ∉ rightHead :: rightTail)
    (valid :
      (Identity.mk (w head (leftHead :: leftTail))
        (w head (rightHead :: rightTail))).SatisfiedBy S5_254.table.semigroup) :
    (Identity.mk (w leftHead leftTail)
      (w rightHead rightTail)).SatisfiedBy S5_254.table.semigroup := by
  intro valuation
  let modified := identityAtHead head valuation
  have full := valid modified
  have fullLeft :=
    S5_254.m18EvalList_toList modified
      (w head (leftHead :: leftTail))
  have fullRight :=
    S5_254.m18EvalList_toList modified
      (w head (rightHead :: rightTail))
  have states :
      S5_254.m18EvalList valuation (leftHead :: leftTail) =
        S5_254.m18EvalList valuation (rightHead :: rightTail) := by
    calc
      S5_254.m18EvalList valuation (leftHead :: leftTail) =
          S5_254.m18EvalList modified (head :: leftHead :: leftTail) := by
            symm
            exact m18EvalList_cons_identity_of_absent head
              (leftHead :: leftTail) (by simp) leftAbsent valuation
      _ = S5_254.m18EvalList modified (head :: rightHead :: rightTail) := by
            exact fullLeft.trans <|
              (congrArg S5_254.M18ListState.value full).trans fullRight.symm
      _ = S5_254.m18EvalList valuation (rightHead :: rightTail) :=
            m18EvalList_cons_identity_of_absent head
              (rightHead :: rightTail) (by simp) rightAbsent valuation
  have tailLeft :=
    S5_254.m18EvalList_toList valuation (w leftHead leftTail)
  have tailRight :=
    S5_254.m18EvalList_toList valuation (w rightHead rightTail)
  exact S5_254.M18ListState.value.inj <|
    tailLeft.symm.trans (states.trans tailRight)

private theorem signatureSymm
    {left right : Word Nat} (same : S5_254.SameM18Signature left right) :
    S5_254.SameM18Signature right left where
  support := fun letter => (same.support letter).symm
  totalParity := fun letter => (same.totalParity letter).symm
  globallySimple := fun letter => (same.globallySimple letter).symm
  prefixParity := fun separator leftSimple rightSimple letter parity =>
    (same.prefixParity separator rightSimple leftSimple letter parity).symm

private theorem eq_singleton_of_signature
    (head : Nat) (word : Word Nat)
    (wordHead : word.head = head)
    (same : S5_254.SameM18Signature (Word.singleton head) word) :
    word = Word.singleton head := by
  cases word with
  | mk rightHead rightTail =>
      change rightHead = head at wordHead
      subst rightHead
      have rightSimple : S5_254.GloballySimple (w head rightTail) head :=
        (same.globallySimple head).mp (by
          simp [S5_254.GloballySimple, Word.toList, Word.singleton])
      have tailNoHead : head ∉ rightTail := by
        rw [← List.count_eq_zero]
        unfold S5_254.GloballySimple at rightSimple
        simp [w, Word.toList] at rightSimple
        omega
      have tailNil : rightTail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter member
        have inRight : letter ∈ (w head rightTail).toList := by
          simp [w, Word.toList, member]
        have inLeft := (same.support letter).mpr inRight
        have equal : letter = head := by
          simpa [Word.toList, Word.singleton] using inLeft
        subst letter
        exact tailNoHead member
      subst rightTail
      rfl

private theorem head_absent_from_tail_of_simple
    (head : Nat) (tail : List Nat)
    (simple : S5_254.GloballySimple (w head tail) head) :
    head ∉ tail := by
  rw [← List.count_eq_zero]
  unfold S5_254.GloballySimple at simple
  simp [w, Word.toList] at simple
  omega

/-! ## Fresh-prefix form of Lee--Zhang Lemma 7.5 -/

private def freshSubstitution
    (fresh : Nat) (replacement : Word Nat) : Nat → Word Nat :=
  fun selected =>
    if selected = fresh then replacement else Word.singleton selected

private theorem flatMap_freshSubstitution_of_not_mem
    (fresh : Nat) (replacement : Word Nat) :
    ∀ letters : List Nat, fresh ∉ letters →
      letters.flatMap
          (fun selected =>
            (freshSubstitution fresh replacement selected).toList) =
        letters
  | [], _ => rfl
  | selected :: rest, absent => by
      have selectedNe : selected ≠ fresh := by
        intro equal
        apply absent
        simp [equal]
      have restAbsent : fresh ∉ rest := by
        intro member
        exact absent (List.Mem.tail selected member)
      rw [List.flatMap_cons,
        flatMap_freshSubstitution_of_not_mem
          fresh replacement rest restAbsent]
      simp [freshSubstitution, selectedNe]

private theorem bind_fresh_prefix
    (word : Word Nat) (fresh : Nat) (replacement : Word Nat)
    (freshAbsent : fresh ∉ word.toList) :
    (Word.singleton fresh ++ word).bind
        (freshSubstitution fresh replacement) =
      replacement ++ word := by
  apply Word.toList_injective
  rw [Word.toList_bind, Word.toList_append,
    Word.toList_singleton, List.flatMap_append,
    flatMap_freshSubstitution_of_not_mem
      fresh replacement word.toList freshAbsent,
    Word.toList_append]
  simp [freshSubstitution]

private def freshAbove : List Nat → Nat
  | [] => 0
  | selected :: rest => max (selected + 1) (freshAbove rest)

private theorem lt_freshAbove_of_mem
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ letters → selected < freshAbove letters
  | [], member => by simp at member
  | head :: rest, member => by
      rcases List.mem_cons.mp member with atHead | inRest
      · subst selected
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self head)
          (Nat.le_max_left (head + 1) (freshAbove rest))
      · exact Nat.lt_of_lt_of_le
          (lt_freshAbove_of_mem selected rest inRest)
          (Nat.le_max_right (head + 1) (freshAbove rest))

private def freshVariable (identity : Identity Nat) : Nat :=
  freshAbove (identity.lhs.toList ++ identity.rhs.toList)

private theorem freshVariable_not_mem_left
    (identity : Identity Nat) :
    freshVariable identity ∉ identity.lhs.toList := by
  intro member
  have impossible :=
    lt_freshAbove_of_mem (freshVariable identity)
      (identity.lhs.toList ++ identity.rhs.toList)
      (List.mem_append.mpr (Or.inl member))
  exact Nat.lt_irrefl _ impossible

private theorem freshVariable_not_mem_right
    (identity : Identity Nat) :
    freshVariable identity ∉ identity.rhs.toList := by
  intro member
  have impossible :=
    lt_freshAbove_of_mem (freshVariable identity)
      (identity.lhs.toList ++ identity.rhs.toList)
      (List.mem_append.mpr (Or.inr member))
  exact Nat.lt_irrefl _ impossible

/-- If the head occurs again, two extra copies immediately before the word
contract away.  This is the derivational step used in Lemma 7.5. -/
private theorem derivesDoublePrefixOfRepeatedHead
    (word : Word Nat)
    (repeated : 2 ≤ word.toList.count word.head) :
    Derives basis
      ((Word.singleton word.head ++ Word.singleton word.head) ++ word)
      word := by
  cases word with
  | mk head tail =>
      change 2 ≤ (head :: tail).count head at repeated
      have inTail : head ∈ tail := by
        rw [List.count_cons_self] at repeated
        exact List.count_pos_iff.mp (by omega)
      obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp inTail
      rw [shape]
      by_cases beforeEmpty : before = []
      · subst before
        apply derives_of_listDerives_toList
        have power :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesFourToTwo (Word.singleton head))
        simpa [Word.toList, Word.singleton, Word.append,
          List.append_assoc] using power.append after
      · obtain ⟨middleHead, middleTail, middleShape⟩ :=
          List.exists_cons_of_ne_nil beforeEmpty
        subst before
        let middle : Word Nat := ⟨middleHead, middleTail⟩
        apply derives_of_listDerives_toList
        have sandwich :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesLeftSandwich (Word.singleton head) middle)
        simpa [middle, Word.toList, Word.singleton, Word.append,
          List.append_assoc] using sandwich.append after

/-! ## Intersection completeness -/

private theorem derives_of_simple_common_head
    (identity : Identity Nat)
    (m18Valid : identity.SatisfiedBy S5_254.table.semigroup)
    (same : S5_254.SameM18Signature identity.lhs identity.rhs)
    (heads : identity.lhs.head = identity.rhs.head)
    (leftSimple : S5_254.GloballySimple identity.lhs identity.lhs.head) :
    Derives basis identity.lhs identity.rhs := by
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              change leftHead = rightHead at heads
              subst rightHead
              have rightSimple :
                  S5_254.GloballySimple (w leftHead rightTail) leftHead :=
                (same.globallySimple leftHead).mp leftSimple
              cases leftTail with
              | nil =>
                  have equal := eq_singleton_of_signature leftHead
                    (w leftHead rightTail) rfl same
                  have tailEqual := congrArg Word.tail equal
                  simp [w, Word.singleton] at tailEqual
                  subst rightTail
                  exact Derives.refl _
              | cons leftNext leftRest =>
                  have rightNonempty : rightTail ≠ [] := by
                    intro rightEmpty
                    subst rightTail
                    have singletonLeft :=
                      eq_singleton_of_signature leftHead
                        (w leftHead (leftNext :: leftRest)) rfl
                        (signatureSymm same)
                    have impossible := congrArg Word.tail singletonLeft
                    simp [w, Word.singleton] at impossible
                  obtain ⟨rightNext, rightRest, rightShape⟩ :=
                    List.exists_cons_of_ne_nil rightNonempty
                  subst rightTail
                  have leftAbsent : leftHead ∉ leftNext :: leftRest :=
                    head_absent_from_tail_of_simple leftHead
                      (leftNext :: leftRest) leftSimple
                  have rightAbsent : leftHead ∉ rightNext :: rightRest :=
                    head_absent_from_tail_of_simple leftHead
                      (rightNext :: rightRest) rightSimple
                  let tailIdentity : Identity Nat :=
                    ⟨w leftNext leftRest, w rightNext rightRest⟩
                  have tailValid :
                      tailIdentity.SatisfiedBy S5_254.table.semigroup := by
                    exact tailIdentity_valid leftHead leftNext rightNext
                      leftRest rightRest leftAbsent rightAbsent m18Valid
                  have tailDerivation :
                      Derives S5_254.basis tailIdentity.lhs tailIdentity.rhs :=
                    S5_254.basisFor.2 tailIdentity tailValid
                  have lifted :=
                    liftM18DerivationAfterPrefix tailDerivation
                      (Word.singleton leftHead) Word.singleton
                  rw [bind_singleton, bind_singleton] at lifted
                  simpa [tailIdentity, w, Word.singleton, Word.append] using
                    lifted

private theorem directIntersectionComplete
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.S2_4.table.semigroup)
    (m18Valid : identity.SatisfiedBy S5_254.table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have heads := heads_eq_of_leftZero_valid identity leftValid
  have same := S5_254.sameM18Signature_of_valid identity m18Valid
  by_cases leftSimple :
      S5_254.GloballySimple identity.lhs identity.lhs.head
  · exact derives_of_simple_common_head identity m18Valid same heads leftSimple
  · have rightNotSimple :
        ¬ S5_254.GloballySimple identity.rhs identity.rhs.head := by
      intro rightSimple
      have rightAtLeftHead :
          S5_254.GloballySimple identity.rhs identity.lhs.head := by
        simpa [heads] using rightSimple
      exact leftSimple ((same.globallySimple identity.lhs.head).mpr
        rightAtLeftHead)
    have leftRepeated : 2 ≤ identity.lhs.toList.count identity.lhs.head := by
      have positive : 0 < identity.lhs.toList.count identity.lhs.head :=
        List.count_pos_iff.mpr (by simp [Word.toList])
      unfold S5_254.GloballySimple at leftSimple
      omega
    have rightRepeated : 2 ≤ identity.rhs.toList.count identity.rhs.head := by
      have positive : 0 < identity.rhs.toList.count identity.rhs.head :=
        List.count_pos_iff.mpr (by simp [Word.toList])
      unfold S5_254.GloballySimple at rightNotSimple
      omega
    let fresh := freshVariable identity
    have freshLeft : fresh ∉ identity.lhs.toList := by
      simpa [fresh] using freshVariable_not_mem_left identity
    have freshRight : fresh ∉ identity.rhs.toList := by
      simpa [fresh] using freshVariable_not_mem_right identity
    have m18Derivation :
        Derives S5_254.basis identity.lhs identity.rhs :=
      S5_254.basisFor.2 identity m18Valid
    have prefixed :=
      liftM18DerivationAfterPrefix m18Derivation
        (Word.singleton fresh) Word.singleton
    rw [bind_singleton, bind_singleton] at prefixed
    let doubleHead :=
      Word.singleton identity.lhs.head ++
        Word.singleton identity.lhs.head
    have substituted :=
      Derives.subst prefixed
        (freshSubstitution fresh doubleHead)
    rw [bind_fresh_prefix identity.lhs fresh doubleHead freshLeft,
      bind_fresh_prefix identity.rhs fresh doubleHead freshRight]
      at substituted
    have leftContractRaw :=
      derivesDoublePrefixOfRepeatedHead identity.lhs leftRepeated
    have rightContractRaw :=
      derivesDoublePrefixOfRepeatedHead identity.rhs rightRepeated
    have leftContract :
        Derives basis (doubleHead ++ identity.lhs) identity.lhs := by
      simpa [doubleHead, Word.append_assoc] using leftContractRaw
    have rightContract :
        Derives basis (doubleHead ++ identity.rhs) identity.rhs := by
      simpa [doubleHead, heads, Word.append_assoc] using rightContractRaw
    exact leftContract.symm.trans <| substituted.trans rightContract

/-- The four X(7.1) laws are the exact intersection basis for `L2` and
`S5_254`. -/
def directIntersection :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      S5_254.table.semigroup basis where
  leftModels := modelsLeftZero
  rightModels := modelsM18
  complete := directIntersectionComplete

/-- The same four laws axiomatize the intersection with the opposite M18
orientation. -/
def oppositeIntersection :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      S5_254.table.semigroup.opposite basis where
  leftModels := modelsLeftZero
  rightModels := modelsM18Opposite
  complete := by
    intro identity leftValid oppositeValid
    exact directIntersectionComplete identity leftValid
      (m18Valid_of_oppositeValid identity oppositeValid)

end SemigroupBasis.CoRoots.Order6LeeZhangClass66

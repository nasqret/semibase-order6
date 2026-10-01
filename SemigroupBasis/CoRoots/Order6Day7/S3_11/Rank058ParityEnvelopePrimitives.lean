import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Exact rank-058 parity-preserving connected-component envelope primitives

Every theorem below is derived only from a literal displayed rank-058 law.
The alternating-span list theorem handles BOTH the empty-filler (`law08`)
and nonempty-filler (`law09`) branches without an invalid empty semigroup
substitution.  None imports the parity-changing lower-factor calculus.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058.ParityEnvelope

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank058.basis

abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

private def word (head : Nat) (tail : List Nat) : Word Nat :=
  Word.mk head tail

private def instantiateThree
    (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | letter + 3 => Word.singleton (letter + 3)

private def instantiateFour
    (first second third fourth : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | 3 => fourth
  | letter + 4 => Word.singleton (letter + 4)

private def surround
    (front : Option (Word Nat)) (middle : Word Nat)
    (suffix : Option (Word Nat)) : Word Nat :=
  match front, suffix with
  | none, none => middle
  | some before, none => before ++ middle
  | none, some after => middle ++ after
  | some before, some after => (before ++ middle) ++ after

private theorem displayedForward
    (identity : Identity Nat) (member : identity ∈ targetBasis)
    (substitution : Nat → Word Nat)
    (front suffix : Option (Word Nat)) :
    Derives targetBasis
      (surround front (identity.lhs.bind substitution) suffix)
      (surround front (identity.rhs.bind substitution) suffix) := by
  have primitive := Derives.subst (Derives.fromBasis member) substitution
  cases front with
  | none =>
      cases suffix with
      | none => exact primitive
      | some after => exact Derives.appendRight primitive after
  | some before =>
      cases suffix with
      | none => exact Derives.prepend before primitive
      | some after =>
          exact Derives.appendRight (Derives.prepend before primitive) after

/-- Literal frozen `xx = xxxx`, used only in its parity-preserving direction. -/
theorem derivesSquarePairContraction
    (anchor : Word Nat) :
    Derives targetBasis
      (((anchor ++ anchor) ++ anchor) ++ anchor)
      (anchor ++ anchor) := by
  have primitive :
      Derives targetBasis (word 0 [0, 0, 0]) (word 0 [0]) :=
    (Derives.fromBasis (e := Rank058.law00)
      (show Rank058.law00 ∈ targetBasis by decide)).symm
  have substituted :=
    Derives.subst primitive (instantiateThree anchor anchor anchor)
  simpa [word, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Literal frozen `xxx y x = x y x`; the anchor multiplicity drops by TWO. -/
theorem derivesAnchorPrefixPairContraction
    (anchor interior : Word Nat) :
    Derives targetBasis
      ((((anchor ++ anchor) ++ anchor) ++ interior) ++ anchor)
      ((anchor ++ interior) ++ anchor) := by
  have primitive :
      Derives targetBasis (word 0 [0, 0, 1, 0]) (word 0 [1, 0]) :=
    Derives.fromBasis (e := Rank058.law01)
      (show Rank058.law01 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree anchor interior interior)
  simpa [word, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Literal frozen balanced `xx y xx = x y x`; endpoint parity is preserved. -/
theorem derivesBalancedAnchorPairContraction
    (anchor interior : Word Nat) :
    Derives targetBasis
      ((((anchor ++ anchor) ++ interior) ++ anchor) ++ anchor)
      ((anchor ++ interior) ++ anchor) := by
  have primitive :
      Derives targetBasis (word 0 [0, 1, 0, 0]) (word 0 [1, 0]) :=
    Derives.fromBasis (e := Rank058.law03)
      (show Rank058.law03 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree anchor interior interior)
  simpa [word, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Literal frozen `x y xxx = x y x`; the closing anchor drops by TWO. -/
theorem derivesAnchorSuffixPairContraction
    (anchor interior : Word Nat) :
    Derives targetBasis
      ((((anchor ++ interior) ++ anchor) ++ anchor) ++ anchor)
      ((anchor ++ interior) ++ anchor) := by
  have primitive :
      Derives targetBasis (word 0 [1, 0, 0, 0]) (word 0 [1, 0]) :=
    (Derives.fromBasis (e := Rank058.law04)
      (show Rank058.law04 ∈ targetBasis by decide)).symm
  have substituted :=
    Derives.subst primitive (instantiateThree anchor interior interior)
  simpa [word, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Literal frozen `x yyy x = x y x`; interior parity is preserved. -/
theorem derivesInteriorTripleContraction
    (anchor repeated : Word Nat) :
    Derives targetBasis
      ((((anchor ++ repeated) ++ repeated) ++ repeated) ++ anchor)
      ((anchor ++ repeated) ++ anchor) := by
  have primitive :
      Derives targetBasis (word 0 [1, 1, 1, 0]) (word 0 [1, 0]) :=
    (Derives.fromBasis (e := Rank058.law07)
      (show Rank058.law07 ∈ targetBasis by decide)).symm
  have substituted :=
    Derives.subst primitive (instantiateThree anchor repeated repeated)
  simpa [word, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Literal frozen `x y x y = x y y x`; closes the empty-filler crossing. -/
theorem derivesEmptyAlternatingSpanExtension
    (anchor crossing : Word Nat) :
    Derives targetBasis
      (((anchor ++ crossing) ++ anchor) ++ crossing)
      (((anchor ++ crossing) ++ crossing) ++ anchor) := by
  have primitive :
      Derives targetBasis (word 0 [1, 0, 1]) (word 0 [1, 1, 0]) :=
    Derives.fromBasis (e := Rank058.law08)
      (show Rank058.law08 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree anchor crossing crossing)
  simpa [word, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Literal frozen `x y x z y = x y y z x`; extends an alternating span. -/
theorem derivesAlternatingSpanExtension
    (anchor crossing filler : Word Nat) :
    Derives targetBasis
      ((((anchor ++ crossing) ++ anchor) ++ filler) ++ crossing)
      ((((anchor ++ crossing) ++ crossing) ++ filler) ++ anchor) := by
  have primitive :
      Derives targetBasis (word 0 [1, 0, 2, 1]) (word 0 [1, 1, 2, 0]) :=
    Derives.fromBasis (e := Rank058.law09)
      (show Rank058.law09 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree anchor crossing filler)
  simpa [word, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Literal frozen `x y z x = x z y x`; rotates complete interior blocks. -/
theorem derivesInteriorBlockRotation
    (anchor left right : Word Nat) :
    Derives targetBasis
      (((anchor ++ left) ++ right) ++ anchor)
      (((anchor ++ right) ++ left) ++ anchor) := by
  have primitive :
      Derives targetBasis (word 0 [1, 2, 0]) (word 0 [2, 1, 0]) :=
    Derives.fromBasis (e := Rank058.law10)
      (show Rank058.law10 ∈ targetBasis by decide)
  have substituted :=
    Derives.subst primitive (instantiateThree anchor left right)
  simpa [word, instantiateThree, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

/-- Five independently typed frozen edges swap protected interior neighbors. -/
theorem derivesInteriorAdjacentTranspositionPrimitive :
    Derives targetBasis
      (word 0 [1, 2, 3, 0])
      (word 0 [2, 1, 3, 0]) := by
  have step00 :
      Derives targetBasis
        (word 0 [1, 2, 3, 0])
        (word 0 [0, 1, 2, 3, 0, 0]) := by
    exact (displayedForward Rank058.law03
      (show Rank058.law03 ∈ targetBasis by decide)
      (instantiateFour (word 0 []) (word 1 [2, 3])
        (word 2 []) (word 3 [])) none none).symm
  have step01 :
      Derives targetBasis
        (word 0 [0, 1, 2, 3, 0, 0])
        (word 0 [3, 0, 0, 1, 2, 0]) := by
    exact displayedForward Rank058.law10
      (show Rank058.law10 ∈ targetBasis by decide)
      (instantiateFour (word 0 []) (word 0 [1, 2])
        (word 3 [0]) (word 3 [])) none none
  have step02 :
      Derives targetBasis
        (word 0 [3, 0, 0, 1, 2, 0])
        (word 0 [3, 0, 0, 2, 1, 0]) := by
    exact displayedForward Rank058.law10
      (show Rank058.law10 ∈ targetBasis by decide)
      (instantiateFour (word 0 []) (word 1 [])
        (word 2 []) (word 3 [])) (some (word 0 [3, 0])) none
  have step03 :
      Derives targetBasis
        (word 0 [3, 0, 0, 2, 1, 0])
        (word 0 [0, 2, 1, 3, 0, 0]) := by
    exact (displayedForward Rank058.law10
      (show Rank058.law10 ∈ targetBasis by decide)
      (instantiateFour (word 0 []) (word 0 [2, 1])
        (word 3 [0]) (word 3 [])) none none).symm
  have step04 :
      Derives targetBasis
        (word 0 [0, 2, 1, 3, 0, 0])
        (word 0 [2, 1, 3, 0]) := by
    exact displayedForward Rank058.law03
      (show Rank058.law03 ∈ targetBasis by decide)
      (instantiateFour (word 0 []) (word 2 [1, 3])
        (word 2 []) (word 3 [])) none none
  exact (((step00.trans step01).trans step02).trans step03).trans step04

/-- The five-edge transposition allows arbitrary NONEMPTY protected blocks. -/
theorem derivesInteriorAdjacentTransposition
    (anchor left right trailing : Word Nat) :
    Derives targetBasis
      ((((anchor ++ left) ++ right) ++ trailing) ++ anchor)
      ((((anchor ++ right) ++ left) ++ trailing) ++ anchor) := by
  have substituted :=
    Derives.subst derivesInteriorAdjacentTranspositionPrimitive
      (instantiateFour anchor left right trailing)
  simpa [word, instantiateFour, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Insert exactly TWO anchors in a protected envelope: three frozen edges. -/
theorem derivesInteriorDoubleAnchorInsertionPrimitive :
    Derives targetBasis
      (word 0 [1, 2, 0])
      (word 0 [1, 0, 0, 2, 0]) := by
  have step00 :
      Derives targetBasis
        (word 0 [1, 2, 0])
        (word 0 [0, 1, 2, 0, 0]) := by
    exact (displayedForward Rank058.law03
      (show Rank058.law03 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 [2]) (word 2 []))
      none none).symm
  have step01 :
      Derives targetBasis
        (word 0 [0, 1, 2, 0, 0])
        (word 0 [0, 2, 1, 0, 0]) := by
    exact displayedForward Rank058.law10
      (show Rank058.law10 ∈ targetBasis by decide)
      (instantiateThree (word 0 [0]) (word 1 []) (word 2 []))
      none none
  have step02 :
      Derives targetBasis
        (word 0 [0, 2, 1, 0, 0])
        (word 0 [1, 0, 0, 2, 0]) := by
    exact (displayedForward Rank058.law10
      (show Rank058.law10 ∈ targetBasis by decide)
      (instantiateThree (word 0 []) (word 1 [0]) (word 0 [2]))
      none none).symm
  exact step00.trans (step01.trans step02)

/-- The three-edge insertion admits arbitrary nonempty substituted blocks. -/
theorem derivesInteriorDoubleAnchorInsertion
    (anchor fixed remainder : Word Nat) :
    Derives targetBasis
      (((anchor ++ fixed) ++ remainder) ++ anchor)
      (((((anchor ++ fixed) ++ anchor) ++ anchor) ++ remainder) ++ anchor) := by
  have substituted :=
    Derives.subst derivesInteriorDoubleAnchorInsertionPrimitive
      (instantiateThree anchor fixed remainder)
  simpa [word, instantiateThree, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using substituted

/-- Extend a crossing interval past its protected nonempty interior. -/
theorem derivesProtectedInteriorSpanExtension
    (anchor crossing interior : Word Nat) :
    Derives targetBasis
      ((((anchor ++ crossing) ++ interior) ++ anchor) ++ crossing)
      ((((anchor ++ crossing) ++ crossing) ++ interior) ++ anchor) := by
  have rotate := Derives.prepend anchor
    (derivesInteriorBlockRotation crossing interior anchor)
  have first :
      Derives targetBasis
        ((((anchor ++ crossing) ++ interior) ++ anchor) ++ crossing)
        ((((anchor ++ crossing) ++ anchor) ++ interior) ++ crossing) := by
    simpa [Word.append_assoc] using rotate
  exact first.trans (derivesAlternatingSpanExtension anchor crossing interior)

/-- Rotate possibly empty interior LIST blocks without illegal empty blocks. -/
theorem listDerivesInteriorBlockRotation
    (anchor : Nat) (left right suffix : List Nat) :
    ListDerives
      (anchor :: left ++ right ++ anchor :: suffix)
      (anchor :: right ++ left ++ anchor :: suffix) := by
  cases left with
  | nil =>
      simpa [List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := targetBasis) (anchor :: right ++ anchor :: suffix))
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          simpa [List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
              (basis := targetBasis)
              (anchor :: leftHead :: leftTail ++ anchor :: suffix))
      | cons rightHead rightTail =>
          have core :=
            derivesInteriorBlockRotation
              (Word.singleton anchor)
              (listWordOfCons leftHead leftTail)
              (listWordOfCons rightHead rightTail)
          have listed :
              ListDerives
                (anchor :: leftHead :: leftTail ++
                  rightHead :: rightTail ++ [anchor])
                (anchor :: rightHead :: rightTail ++
                  leftHead :: leftTail ++ [anchor]) :=
            SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
              simpa [listWordOfCons, Word.singleton, Word.append,
                Word.append_assoc, List.append_assoc] using core
          simpa [List.append_assoc] using listed.append suffix

/-- Extend an alternating support interval, for EMPTY or NONEMPTY fillers. -/
theorem listDerivesAlternatingSpanExtension
    (anchor crossing : Nat) (filler suffix : List Nat) :
    ListDerives
      (anchor :: crossing :: anchor :: filler ++ crossing :: suffix)
      (anchor :: crossing :: crossing :: filler ++ anchor :: suffix) := by
  cases filler with
  | nil =>
      have core :=
        derivesEmptyAlternatingSpanExtension
          (Word.singleton anchor) (Word.singleton crossing)
      have listed :
          ListDerives
            [anchor, crossing, anchor, crossing]
            [anchor, crossing, crossing, anchor] :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [Word.singleton, Word.append, Word.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix
  | cons fillerHead fillerTail =>
      have core :=
        derivesAlternatingSpanExtension
          (Word.singleton anchor) (Word.singleton crossing)
          (listWordOfCons fillerHead fillerTail)
      have listed :
          ListDerives
            (anchor :: crossing :: anchor :: fillerHead ::
              fillerTail ++ [crossing])
            (anchor :: crossing :: crossing :: fillerHead ::
              fillerTail ++ [anchor]) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix

/-- Remove exactly TWO initial endpoint copies for every possible interior. -/
theorem listDerivesAnchorPrefixPairContraction
    (anchor : Nat) (interior suffix : List Nat) :
    ListDerives
      (anchor :: anchor :: anchor :: interior ++ anchor :: suffix)
      (anchor :: interior ++ anchor :: suffix) := by
  cases interior with
  | nil =>
      have core := derivesSquarePairContraction (Word.singleton anchor)
      have listed :
          ListDerives [anchor, anchor, anchor, anchor] [anchor, anchor] :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [Word.singleton, Word.append, Word.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix
  | cons interiorHead interiorTail =>
      have core :=
        derivesAnchorPrefixPairContraction
          (Word.singleton anchor) (listWordOfCons interiorHead interiorTail)
      have listed :
          ListDerives
            (anchor :: anchor :: anchor :: interiorHead ::
              interiorTail ++ [anchor])
            (anchor :: interiorHead :: interiorTail ++ [anchor]) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix

/-- Insert TWO anchors after a fixed letter, including the empty remainder. -/
theorem listDerivesInteriorDoubleAnchorInsertion
    (anchor fixed : Nat) (remainder suffix : List Nat) :
    ListDerives
      (anchor :: fixed :: remainder ++ anchor :: suffix)
      (anchor :: fixed :: anchor :: anchor :: remainder ++ anchor :: suffix) := by
  cases remainder with
  | nil =>
      have core :=
        (derivesAnchorSuffixPairContraction
          (Word.singleton anchor) (Word.singleton fixed)).symm
      have listed :
          ListDerives
            [anchor, fixed, anchor]
            [anchor, fixed, anchor, anchor, anchor] :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [Word.singleton, Word.append, Word.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix
  | cons remainderHead remainderTail =>
      have core :=
        derivesInteriorDoubleAnchorInsertion
          (Word.singleton anchor) (Word.singleton fixed)
          (listWordOfCons remainderHead remainderTail)
      have listed :
          ListDerives
            (anchor :: fixed :: remainderHead ::
              remainderTail ++ [anchor])
            (anchor :: fixed :: anchor :: anchor :: remainderHead ::
              remainderTail ++ [anchor]) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix

/-- Swap adjacent interior letters while retaining every protected suffix. -/
theorem listDerivesInteriorAdjacentTransposition
    (anchor left right : Nat) (remaining suffix : List Nat) :
    ListDerives
      (anchor :: left :: right :: remaining ++ anchor :: suffix)
      (anchor :: right :: left :: remaining ++ anchor :: suffix) := by
  cases remaining with
  | nil =>
      simpa [List.append_assoc] using
        listDerivesInteriorBlockRotation anchor [left] [right] suffix
  | cons remainingHead remainingTail =>
      have core :=
        derivesInteriorAdjacentTransposition
          (Word.singleton anchor) (Word.singleton left)
          (Word.singleton right)
          (listWordOfCons remainingHead remainingTail)
      have listed :
          ListDerives
            (anchor :: left :: right :: remainingHead ::
              remainingTail ++ [anchor])
            (anchor :: right :: left :: remainingHead ::
              remainingTail ++ [anchor]) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix

/-- Lift an envelope derivation past a fixed letter using an EVEN insertion. -/
theorem listDerivesInteriorCons
    (anchor letter : Nat) (suffix : List Nat)
    {left right : List Nat}
    (derivation :
      ListDerives
        (anchor :: left ++ anchor :: suffix)
        (anchor :: right ++ anchor :: suffix)) :
    ListDerives
      (anchor :: letter :: left ++ anchor :: suffix)
      (anchor :: letter :: right ++ anchor :: suffix) := by
  have first :=
    listDerivesInteriorDoubleAnchorInsertion anchor letter left suffix
  have second :
      ListDerives
        (anchor :: letter :: anchor :: anchor :: left ++ anchor :: suffix)
        (anchor :: letter :: anchor :: anchor :: right ++ anchor :: suffix) := by
    simpa [List.append_assoc] using
      derivation.prepend [anchor, letter, anchor]
  have third :=
    (listDerivesInteriorDoubleAnchorInsertion anchor letter right suffix).symm
  exact first.trans (second.trans third)

/-- FULL unrestricted parity-preserving interior permutation induction. -/
theorem listDerivesInteriorPermutation
    (anchor : Nat) (suffix : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    ListDerives
      (anchor :: left ++ anchor :: suffix)
      (anchor :: right ++ anchor :: suffix) := by
  induction permutation with
  | nil =>
      exact SemigroupBasis.CoRoots.S5_107.ListDerives.refl _
  | cons letter _ induction =>
      exact listDerivesInteriorCons anchor letter suffix induction
  | swap first second remaining =>
      exact listDerivesInteriorAdjacentTransposition
        anchor second first remaining suffix
  | trans _ _ first second =>
      exact first.trans second

/-- Merge an alternating crossing, handling empty AND nonempty protected gaps. -/
theorem listDerivesProtectedInteriorSpanExtension
    (anchor crossing : Nat) (interior suffix : List Nat) :
    ListDerives
      (anchor :: crossing :: interior ++ anchor :: crossing :: suffix)
      (anchor :: crossing :: crossing :: interior ++ anchor :: suffix) := by
  cases interior with
  | nil =>
      have core :=
        derivesEmptyAlternatingSpanExtension
          (Word.singleton anchor) (Word.singleton crossing)
      have listed :
          ListDerives
            [anchor, crossing, anchor, crossing]
            [anchor, crossing, crossing, anchor] :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [Word.singleton, Word.append, Word.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix
  | cons interiorHead interiorTail =>
      have core :=
        derivesProtectedInteriorSpanExtension
          (Word.singleton anchor) (Word.singleton crossing)
          (listWordOfCons interiorHead interiorTail)
      have listed :
          ListDerives
            (anchor :: crossing :: interiorHead :: interiorTail ++
              anchor :: [crossing])
            (anchor :: crossing :: crossing :: interiorHead ::
              interiorTail ++ [anchor]) :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.words <| by
          simpa [listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using core
      simpa [List.append_assoc] using listed.append suffix

end SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058.ParityEnvelope

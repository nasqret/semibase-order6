import SemigroupBasis.CoRoots.S5_107
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.CoRoots.S5_107Syntax

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

/-- The existing four-to-two block contraction, exposed at list level. -/
theorem listDerivesFourToTwo (u : Word Nat) :
    ListDerives basis
      ((((u ++ u) ++ u) ++ u).toList)
      ((u ++ u).toList) :=
  ListDerives.ofWord (derivesFourToTwo u)

/-- Three-to-two block contraction at list level. -/
theorem listDerivesThreeToTwo (u : Word Nat) :
    ListDerives basis
      (((u ++ u) ++ u).toList)
      ((u ++ u).toList) :=
  ListDerives.ofWord (derivesThreeToTwo u)

/-- Lee's left contraction, exposed at list level for normalization code. -/
theorem listDerivesTripleLeftContraction (u v : Word Nat) :
    ListDerives basis
      (((((u ++ u) ++ u) ++ v) ++ u).toList)
      (((u ++ v) ++ u).toList) :=
  ListDerives.ofWord (derivesTripleLeftContraction u v)

/-- Lee's endpoint transfer, exposed at list level. -/
theorem listDerivesEndpointTransfer (u v : Word Nat) :
    ListDerives basis
      ((((u ++ u) ++ v) ++ u).toList)
      (((u ++ v) ++ (u ++ u)).toList) :=
  ListDerives.ofWord (derivesEndpointTransfer u v)

/-- Lee's square move, exposed at list level. -/
theorem listDerivesSquareMove (u v z : Word Nat) :
    ListDerives basis
      (((((u ++ u) ++ v) ++ z) ++ z).toList)
      ((((u ++ v) ++ (z ++ z)) ++ u).toList) :=
  ListDerives.ofWord (derivesSquareMove u v z)

/-- The anchored block transposition, exposed at list level. -/
theorem listDerivesAnchoredBlockSwapWords
    (anchor left right : Word Nat) :
    ListDerives basis
      (((((anchor ++ left) ++ anchor) ++ right) ++ anchor).toList)
      (((((anchor ++ right) ++ anchor) ++ left) ++ anchor).toList) :=
  ListDerives.ofWord
    (derivesAnchoredBlockSwap anchor left right)

/-- A recursively presented run containing at least two copies of `block`.
The parameter records the number of additional copies. -/
def repeatBlockAtLeastTwo (block : List Nat) : Nat → List Nat
  | 0 => block ++ block
  | extra + 1 => block ++ repeatBlockAtLeastTwo block extra

/-- Every adjacent run of at least two copies of a nonempty block contracts
to exactly two copies. -/
theorem listDerivesRepeatBlockAtLeastTwoToTwo
    (head : Nat) (tail : List Nat) :
    ∀ extra : Nat,
      ListDerives basis
        (repeatBlockAtLeastTwo (head :: tail) extra)
        ((head :: tail) ++ (head :: tail))
  | 0 => ListDerives.refl _
  | extra + 1 => by
      let block := head :: tail
      have first :=
        (listDerivesRepeatBlockAtLeastTwoToTwo
          head tail extra).prepend block
      have finish :
          ListDerives basis
            (block ++ (block ++ block))
            (block ++ block) := by
        simpa [block, listWordOfCons, List.append_assoc] using
          (listDerivesThreeToTwo
            (listWordOfCons head tail))
      simpa [repeatBlockAtLeastTwo, block] using
        first.trans finish

/-- Adjacent rendered letter-squares can be transposed. -/
theorem listDerivesSquareBlockCommutation
    (left right : Nat) :
    ListDerives basis
      (renderMultipleSquares [left, right])
      (renderMultipleSquares [right, left]) := by
  simpa [renderMultipleSquares, List.append_assoc] using
    (ListDerives.ofWord <|
      derivesSquareBlockCommutation
        (Word.singleton left) (Word.singleton right))

/-- Any permutation of a list of rendered letter-squares is derivable. -/
theorem listDerivesMultipleSquarePermutation
    {source target : List Nat}
    (permutation : source.Perm target) :
    ListDerives basis
      (renderMultipleSquares source)
      (renderMultipleSquares target) := by
  induction permutation with
  | nil =>
      exact .empty
  | cons letter _ ih =>
      simpa [renderMultipleSquares] using
        ih.prepend [letter, letter]
  | swap left right rest =>
      have swapped :=
        listDerivesSquareBlockCommutation left right
      simpa [renderMultipleSquares] using
        (swapped.append
          (renderMultipleSquares rest)).symm
  | trans _ _ ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

/-- Deterministic ascending order for the labels of a square tail. -/
def sortedSquareLabels (letters : List Nat) : List Nat :=
  letters.mergeSort
    (fun left right : Nat => decide (left ≤ right))

theorem sortedSquareLabels_perm (letters : List Nat) :
    (sortedSquareLabels letters).Perm letters := by
  exact List.mergeSort_perm _ _

/-- Sort a rendered square tail by derivable square commutations. -/
theorem listDerivesSortMultipleSquares (letters : List Nat) :
    ListDerives basis
      (renderMultipleSquares letters)
      (renderMultipleSquares (sortedSquareLabels letters)) :=
  listDerivesMultipleSquarePermutation
    (sortedSquareLabels_perm letters).symm

/-- Transpose two adjacent nonempty blocks between copies of a singleton
anchor. -/
theorem listDerivesAnchoredBlockSwap
    (anchor leftHead rightHead : Nat)
    (leftTail rightTail : List Nat) :
    ListDerives basis
      ([anchor] ++
        renderAnchoredBlocks anchor
          [leftHead :: leftTail, rightHead :: rightTail])
      ([anchor] ++
        renderAnchoredBlocks anchor
          [rightHead :: rightTail, leftHead :: leftTail]) := by
  simpa [renderAnchoredBlocks, listWordOfCons,
    List.append_assoc] using
      (listDerivesAnchoredBlockSwapWords
        (Word.singleton anchor)
        (listWordOfCons leftHead leftTail)
        (listWordOfCons rightHead rightTail))

/-- Every permutation of nonempty blocks is derivable when the blocks are
rendered after a repeated singleton anchor. -/
theorem listDerivesAnchoredBlockPermutation
    (anchor : Nat) {source target : List (List Nat)}
    (permutation : source.Perm target) :
    ∀ suffix : List Nat,
      (∀ block ∈ source, block ≠ []) →
      ListDerives basis
        ([anchor] ++
          renderAnchoredBlocks anchor source ++ suffix)
        ([anchor] ++
          renderAnchoredBlocks anchor target ++ suffix) := by
  induction permutation with
  | nil =>
      intro suffix _
      simpa [renderAnchoredBlocks] using
        (ListDerives.refl (basis := basis) ([anchor] ++ suffix))
  | @cons block source target permutation ih =>
      intro suffix nonempty
      have tailNonempty :
          ∀ candidate ∈ source, candidate ≠ [] := by
        intro candidate member
        exact nonempty candidate
          (List.mem_cons_of_mem block member)
      have tailStep := ih suffix tailNonempty
      simpa [renderAnchoredBlocks, List.append_assoc] using
        tailStep.prepend ([anchor] ++ block)
  | swap left right rest =>
      intro suffix nonempty
      have leftNonempty : left ≠ [] :=
        nonempty left (by simp)
      have rightNonempty : right ≠ [] :=
        nonempty right (by simp)
      rcases List.exists_cons_of_ne_nil leftNonempty with
        ⟨leftHead, leftTail, rfl⟩
      rcases List.exists_cons_of_ne_nil rightNonempty with
        ⟨rightHead, rightTail, rfl⟩
      have swapped :=
        listDerivesAnchoredBlockSwap
          anchor leftHead rightHead leftTail rightTail
      simpa [renderAnchoredBlocks, List.append_assoc] using
        (swapped.append
          (renderAnchoredBlocks anchor rest ++ suffix)).symm
  | @trans source middle target first second ihFirst ihSecond =>
      intro suffix nonempty
      have middleNonempty :
          ∀ block ∈ middle, block ≠ [] := by
        intro block member
        exact nonempty block (first.mem_iff.mpr member)
      exact
        (ihFirst suffix nonempty).trans
          (ihSecond suffix middleNonempty)

/-- Sort the interior simple blocks lexicographically by anchored block
transpositions. -/
theorem listDerivesSortAnchoredBlocks
    (anchor : Nat) (blocks : List (List Nat)) (suffix : List Nat)
    (nonempty : ∀ block ∈ blocks, block ≠ []) :
    ListDerives basis
      ([anchor] ++
        renderAnchoredBlocks anchor blocks ++ suffix)
      ([anchor] ++
        renderAnchoredBlocks anchor
          (sortedSimpleBlocks blocks) ++ suffix) := by
  have permutation :
      blocks.Perm (sortedSimpleBlocks blocks) := by
    unfold sortedSimpleBlocks
    exact (List.mergeSort_perm _ _).symm
  exact
    listDerivesAnchoredBlockPermutation
      anchor permutation suffix nonempty

/-- Independently permute the anchored simple blocks and the square labels in
an already extracted canonical core. -/
theorem listDerivesRenderedCanonicalCore
    (initial final : List Nat) (anchor : Nat)
    {sourceBlocks targetBlocks : List (List Nat)}
    {sourceMultiples targetMultiples : List Nat}
    (blockPermutation : sourceBlocks.Perm targetBlocks)
    (multiplePermutation : sourceMultiples.Perm targetMultiples)
    (blocksNonempty : ∀ block ∈ sourceBlocks, block ≠ []) :
    ListDerives basis
      (initial ++ [anchor] ++
        renderAnchoredBlocks anchor sourceBlocks ++
        renderMultipleSquares sourceMultiples ++ final)
      (initial ++ [anchor] ++
        renderAnchoredBlocks anchor targetBlocks ++
        renderMultipleSquares targetMultiples ++ final) := by
  let middle : List Nat :=
    initial ++ [anchor] ++
      renderAnchoredBlocks anchor targetBlocks ++
      renderMultipleSquares sourceMultiples ++ final
  have blockStep :=
    (listDerivesAnchoredBlockPermutation
      anchor blockPermutation
      (renderMultipleSquares sourceMultiples ++ final)
      blocksNonempty).prepend initial
  have blockStep' :
      ListDerives basis
        (initial ++ [anchor] ++
          renderAnchoredBlocks anchor sourceBlocks ++
          renderMultipleSquares sourceMultiples ++ final)
        middle := by
    dsimp [middle]
    simpa [List.append_assoc] using blockStep
  have squareStep :=
    (listDerivesMultipleSquarePermutation
      multiplePermutation).context
        (initial ++ [anchor] ++
          renderAnchoredBlocks anchor targetBlocks)
        final
  have squareStep' :
      ListDerives basis middle
        (initial ++ [anchor] ++
          renderAnchoredBlocks anchor targetBlocks ++
          renderMultipleSquares targetMultiples ++ final) := by
    dsimp [middle]
    simpa [List.append_assoc] using squareStep
  exact blockStep'.trans squareStep'

/-- Sort both components of an already extracted canonical core. -/
theorem listDerivesSortRenderedCanonicalCore
    (initial final : List Nat) (anchor : Nat)
    (blocks : List (List Nat)) (multiples : List Nat)
    (blocksNonempty : ∀ block ∈ blocks, block ≠ []) :
    ListDerives basis
      (initial ++ [anchor] ++
        renderAnchoredBlocks anchor blocks ++
        renderMultipleSquares multiples ++ final)
      (initial ++ [anchor] ++
        renderAnchoredBlocks anchor
          (sortedSimpleBlocks blocks) ++
        renderMultipleSquares
          (sortedSquareLabels multiples) ++ final) := by
  apply listDerivesRenderedCanonicalCore
  · unfold sortedSimpleBlocks
    exact (List.mergeSort_perm _ _).symm
  · exact (sortedSquareLabels_perm multiples).symm
  · exact blocksNonempty

/-- The no-multiple branch of `simpleAdjacencyCanonicalList` is already in
canonical form. -/
theorem listDerivesToSimpleAdjacencyCanonicalListOfNoMultiples
    (letters : List Nat)
    (noMultiples : sortedMultipleLetters letters = []) :
    ListDerives basis letters
      (simpleAdjacencyCanonicalList letters) := by
  unfold simpleAdjacencyCanonicalList
  rw [noMultiples]
  exact ListDerives.refl _

/-- Conditional completion of the nontrivial canonicalization branch from an
actual extraction derivation. Once an arbitrary word has been derived to an
anchored rendering with exactly two copies of every multiple letter, the
block and square permutations proved above finish the canonical derivation. -/
theorem listDerivesToSimpleAdjacencyCanonicalListOfExtracted
    (letters : List Nat) (anchor : Nat)
    (remainingMultiples : List Nat)
    (sourceBlocks : List (List Nat))
    (sourceMultiples : List Nat)
    (multiplesShape :
      sortedMultipleLetters letters =
        anchor :: remainingMultiples)
    (extracted :
      ListDerives basis letters
        (initialSimpleBlock letters ++ [anchor] ++
          renderAnchoredBlocks anchor sourceBlocks ++
          renderMultipleSquares sourceMultiples ++
          finalSimpleBlock letters))
    (blockPermutation :
      sourceBlocks.Perm
        (sortedSimpleBlocks
          (interiorSimpleBlocks letters)))
    (multiplePermutation :
      sourceMultiples.Perm
        (anchor :: remainingMultiples))
    (blocksNonempty :
      ∀ block ∈ sourceBlocks, block ≠ []) :
    ListDerives basis letters
      (simpleAdjacencyCanonicalList letters) := by
  let target : List Nat :=
    initialSimpleBlock letters ++ [anchor] ++
      renderAnchoredBlocks anchor
        (sortedSimpleBlocks
          (interiorSimpleBlocks letters)) ++
      renderMultipleSquares
        (anchor :: remainingMultiples) ++
      finalSimpleBlock letters
  have core :
      ListDerives basis
        (initialSimpleBlock letters ++ [anchor] ++
          renderAnchoredBlocks anchor sourceBlocks ++
          renderMultipleSquares sourceMultiples ++
          finalSimpleBlock letters)
        target := by
    dsimp [target]
    exact
      listDerivesRenderedCanonicalCore
        (initialSimpleBlock letters)
        (finalSimpleBlock letters) anchor
        blockPermutation multiplePermutation blocksNonempty
  have fromLetters :
      ListDerives basis letters target :=
    extracted.trans core
  have targetEq :
      target = simpleAdjacencyCanonicalList letters := by
    dsimp [target]
    unfold simpleAdjacencyCanonicalList
    rw [multiplesShape]
  rw [targetEq] at fromLetters
  exact fromLetters

/-- Equality-specialized wrapper for a word that is already literally in an
anchored-square rendering. -/
theorem listDerivesToSimpleAdjacencyCanonicalListOfRendered
    (letters : List Nat) (anchor : Nat)
    (remainingMultiples : List Nat)
    (sourceBlocks : List (List Nat))
    (sourceMultiples : List Nat)
    (multiplesShape :
      sortedMultipleLetters letters =
        anchor :: remainingMultiples)
    (rendered :
      letters =
        initialSimpleBlock letters ++ [anchor] ++
          renderAnchoredBlocks anchor sourceBlocks ++
          renderMultipleSquares sourceMultiples ++
          finalSimpleBlock letters)
    (blockPermutation :
      sourceBlocks.Perm
        (sortedSimpleBlocks
          (interiorSimpleBlocks letters)))
    (multiplePermutation :
      sourceMultiples.Perm
        (anchor :: remainingMultiples))
    (blocksNonempty :
      ∀ block ∈ sourceBlocks, block ≠ []) :
    ListDerives basis letters
      (simpleAdjacencyCanonicalList letters) := by
  let renderedList : List Nat :=
    initialSimpleBlock letters ++ [anchor] ++
      renderAnchoredBlocks anchor sourceBlocks ++
      renderMultipleSquares sourceMultiples ++
      finalSimpleBlock letters
  have renderedEq : letters = renderedList := by
    simpa [renderedList] using rendered
  have sourceTypeEq :
      ListDerives basis letters renderedList =
        ListDerives basis renderedList renderedList :=
    congrArg
      (fun source => ListDerives basis source renderedList)
      renderedEq
  have extractedAtRenderedList :
      ListDerives basis letters renderedList :=
    Eq.mpr sourceTypeEq
      (ListDerives.refl renderedList)
  have extracted :
      ListDerives basis
        letters
        (initialSimpleBlock letters ++ [anchor] ++
          renderAnchoredBlocks anchor sourceBlocks ++
          renderMultipleSquares sourceMultiples ++
          finalSimpleBlock letters) := by
    simpa [renderedList] using extractedAtRenderedList
  exact
    listDerivesToSimpleAdjacencyCanonicalListOfExtracted
      letters anchor remainingMultiples sourceBlocks
      sourceMultiples multiplesShape extracted
      blockPermutation multiplePermutation blocksNonempty

/-- Integration bridge from list normalization to the final word-level
derivation. The sole premise is exactly the remaining arbitrary-list
normalization theorem. -/
theorem derivesCanonical
    (word : Word Nat)
    (normalize :
      ListDerives basis word.toList
        (simpleAdjacencyCanonicalList word.toList)) :
    Derives basis word
      (simpleAdjacencyCanonicalWord word) := by
  cases word with
  | mk head tail =>
      have listDerivation :
          ListDerives basis (head :: tail)
            (simpleAdjacencyCanonicalList
              (Word.mk head tail).toList) := by
        simpa [Word.toList] using normalize
      obtain
        ⟨targetHead, targetTail, targetListEq, wordDerivation⟩ :=
          ListDerives.from_cons listDerivation
      have targetWordEq :
          listWordOfCons targetHead targetTail =
            simpleAdjacencyCanonicalWord
              (Word.mk head tail) := by
        apply Word.toList_injective
        rw [toList_simpleAdjacencyCanonicalWord]
        simpa [listWordOfCons] using targetListEq.symm
      rw [targetWordEq] at wordDerivation
      simpa [listWordOfCons] using wordDerivation

/-- Word-level canonicalization for the branch with no multiple variable. -/
theorem derivesCanonicalOfNoMultiples
    (word : Word Nat)
    (noMultiples :
      sortedMultipleLetters word.toList = []) :
    Derives basis word
      (simpleAdjacencyCanonicalWord word) :=
  derivesCanonical word <|
    listDerivesToSimpleAdjacencyCanonicalListOfNoMultiples
      word.toList noMultiples

/-- Word-level canonicalization from an explicit anchored-square extraction
derivation. -/
theorem derivesCanonicalOfExtracted
    (word : Word Nat) (anchor : Nat)
    (remainingMultiples : List Nat)
    (sourceBlocks : List (List Nat))
    (sourceMultiples : List Nat)
    (multiplesShape :
      sortedMultipleLetters word.toList =
        anchor :: remainingMultiples)
    (extracted :
      ListDerives basis word.toList
        (initialSimpleBlock word.toList ++ [anchor] ++
          renderAnchoredBlocks anchor sourceBlocks ++
          renderMultipleSquares sourceMultiples ++
          finalSimpleBlock word.toList))
    (blockPermutation :
      sourceBlocks.Perm
        (sortedSimpleBlocks
          (interiorSimpleBlocks word.toList)))
    (multiplePermutation :
      sourceMultiples.Perm
        (anchor :: remainingMultiples))
    (blocksNonempty :
      ∀ block ∈ sourceBlocks, block ≠ []) :
    Derives basis word
      (simpleAdjacencyCanonicalWord word) :=
  derivesCanonical word <|
    listDerivesToSimpleAdjacencyCanonicalListOfExtracted
      word.toList anchor remainingMultiples
      sourceBlocks sourceMultiples multiplesShape extracted
      blockPermutation multiplePermutation blocksNonempty

/-- Word-level endpoint for a supplied anchored-square decomposition. This is
the integration form used until the unrestricted extraction theorem is
available. -/
theorem derivesCanonicalOfRendered
    (word : Word Nat) (anchor : Nat)
    (remainingMultiples : List Nat)
    (sourceBlocks : List (List Nat))
    (sourceMultiples : List Nat)
    (multiplesShape :
      sortedMultipleLetters word.toList =
        anchor :: remainingMultiples)
    (rendered :
      word.toList =
        initialSimpleBlock word.toList ++ [anchor] ++
          renderAnchoredBlocks anchor sourceBlocks ++
          renderMultipleSquares sourceMultiples ++
          finalSimpleBlock word.toList)
    (blockPermutation :
      sourceBlocks.Perm
        (sortedSimpleBlocks
          (interiorSimpleBlocks word.toList)))
    (multiplePermutation :
      sourceMultiples.Perm
        (anchor :: remainingMultiples))
    (blocksNonempty :
      ∀ block ∈ sourceBlocks, block ≠ []) :
    Derives basis word
      (simpleAdjacencyCanonicalWord word) :=
  derivesCanonical word <|
    listDerivesToSimpleAdjacencyCanonicalListOfRendered
      word.toList anchor remainingMultiples
      sourceBlocks sourceMultiples multiplesShape rendered
      blockPermutation multiplePermutation blocksNonempty

end SemigroupBasis.CoRoots.S5_107

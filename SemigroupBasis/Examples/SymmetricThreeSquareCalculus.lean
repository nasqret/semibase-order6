import SemigroupBasis.Examples.SymmetricThreePrelude

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- A product of square blocks, with a sixth power representing the empty
product in the positive-word language. -/
def symmetricThreeSquareProduct
    (identityRepresentative : Word Nat) : List (Word Nat) → Word Nat
  | [] => symmetricThreeSixthPower identityRepresentative
  | word :: rest =>
      symmetricThreeSquare word ++
        symmetricThreeSquareProduct identityRepresentative rest

/-- Three copies of a square block collapse to the chosen positive-word
identity representative on their left. -/
theorem symmetricThreeDerivesCancelThreeSquaresLeft
    (word suffix : Word Nat) :
    Derives symmetricThreeBasis
      (symmetricThreeSquare word ++
        (symmetricThreeSquare word ++
          (symmetricThreeSquare word ++ suffix)))
      suffix := by
  simpa [symmetricThreeSquare, symmetricThreeSixthPower,
    symmetricThreeFifthPower, Word.append_assoc] using
      symmetricThreeDerivesSixthLeftIdentity word suffix

/-- Three copies of a square block collapse on the right as well. -/
theorem symmetricThreeDerivesCancelThreeSquaresRight
    (stem word : Word Nat) :
    Derives symmetricThreeBasis
      (((stem ++ symmetricThreeSquare word) ++
        symmetricThreeSquare word) ++ symmetricThreeSquare word)
      stem := by
  simpa [symmetricThreeSquare, symmetricThreeSixthPower,
    symmetricThreeFifthPower, Word.append_assoc] using
      symmetricThreeDerivesSixthRightIdentity word stem

/-- Square blocks can be swapped inside arbitrary nonempty contexts. -/
theorem symmetricThreeDerivesSwapSquareBlocks
    (stem first second suffix : Word Nat) :
    Derives symmetricThreeBasis
      ((stem ++ symmetricThreeSquare first) ++
        (symmetricThreeSquare second ++ suffix))
      ((stem ++ symmetricThreeSquare second) ++
        (symmetricThreeSquare first ++ suffix)) := by
  have swapped :=
    Derives.appendRight
      (Derives.prepend stem
        (symmetricThreeDerivesCommuteSquares first second)) suffix
  simpa [Word.append_assoc] using swapped

/-- Permuting the list of square blocks does not change its represented word
modulo the basis. -/
theorem symmetricThreeDerivesSquareProductPermutation
    (identityRepresentative : Word Nat) {first second : List (Word Nat)}
    (permutation : first.Perm second) :
    Derives symmetricThreeBasis
      (symmetricThreeSquareProduct identityRepresentative first)
      (symmetricThreeSquareProduct identityRepresentative second) := by
  induction permutation with
  | nil =>
      exact Derives.refl _
  | cons word _ ih =>
      simpa [symmetricThreeSquareProduct] using
        Derives.prepend (symmetricThreeSquare word) ih
  | swap first second rest =>
      have swapped :=
        Derives.appendRight
          (symmetricThreeDerivesCommuteSquares first second)
          (symmetricThreeSquareProduct identityRepresentative rest)
      simpa [symmetricThreeSquareProduct, Word.append_assoc] using swapped.symm
  | trans _ _ ihFirst ihSecond =>
      exact Derives.trans ihFirst ihSecond

/-- Retain zero, one, or two copies of each square atom according to its
multiplicity modulo three. -/
def symmetricThreeTernaryReduce :
    List (Word Nat) → List (Word Nat)
  | [] => []
  | word :: rest =>
      let reduced := symmetricThreeTernaryReduce rest
      if reduced.count word < 2 then word :: reduced
      else (reduced.erase word).erase word

theorem symmetricThreeCountTernaryReduce
    (tested : Word Nat) (words : List (Word Nat)) :
    (symmetricThreeTernaryReduce words).count tested =
      words.count tested % 3 := by
  induction words generalizing tested with
  | nil =>
      simp [symmetricThreeTernaryReduce]
  | cons word rest ih =>
      simp only [symmetricThreeTernaryReduce]
      split <;> rename_i countBound
      · by_cases same : tested = word
        · subst tested
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at countBound
          omega
        · rw [List.count_cons_of_ne (Ne.symm same),
            List.count_cons_of_ne (Ne.symm same), ih]
      · have reducedBound :
            (symmetricThreeTernaryReduce rest).count word < 3 := by
          rw [ih word]
          exact Nat.mod_lt _ (by decide)
        have reducedCount :
            (symmetricThreeTernaryReduce rest).count word = 2 := by
          omega
        by_cases same : tested = word
        · subst tested
          have countMod : rest.count word % 3 = 2 := by
            rw [← ih word]
            exact reducedCount
          rw [List.count_erase_self, List.count_erase_self,
            List.count_cons_self, reducedCount]
          simp [Nat.add_mod, countMod]
        · rw [List.count_erase_of_ne same,
            List.count_erase_of_ne same,
            List.count_cons_of_ne (Ne.symm same), ih]

theorem symmetricThreeTernaryReduce_perm_of_mod_eq
    {first second : List (Word Nat)}
    (counts : ∀ word, first.count word % 3 = second.count word % 3) :
    (symmetricThreeTernaryReduce first).Perm
      (symmetricThreeTernaryReduce second) := by
  rw [List.perm_iff_count]
  intro word
  rw [symmetricThreeCountTernaryReduce,
    symmetricThreeCountTernaryReduce, counts word]

private theorem symmetricThree_two_copies_perm
    (word : Word Nat) (words : List (Word Nat))
    (count : words.count word = 2) :
    words.Perm (word :: word :: (words.erase word).erase word) := by
  have member : word ∈ words := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase member
  have erasedCount : (words.erase word).count word = 1 := by
    rw [List.count_erase_self]
    omega
  have erasedMember : word ∈ words.erase word :=
    List.count_pos_iff.mp (by omega)
  exact first.trans
    (List.Perm.cons word (List.perm_cons_erase erasedMember))

/-- Every square product derives its canonical modulo-three multiplicity
reduction. -/
theorem symmetricThreeDerivesSquareProductReduction
    (identityRepresentative : Word Nat) :
    ∀ words : List (Word Nat),
      Derives symmetricThreeBasis
        (symmetricThreeSquareProduct identityRepresentative words)
        (symmetricThreeSquareProduct identityRepresentative
          (symmetricThreeTernaryReduce words))
  | [] => by
      exact Derives.refl _
  | word :: rest => by
      have suffix :=
        symmetricThreeDerivesSquareProductReduction
          identityRepresentative rest
      have prefixed :=
        Derives.prepend (symmetricThreeSquare word) suffix
      by_cases countBound :
          (symmetricThreeTernaryReduce rest).count word < 2
      · simpa [symmetricThreeSquareProduct,
          symmetricThreeTernaryReduce, countBound] using prefixed
      · have reducedBound :
            (symmetricThreeTernaryReduce rest).count word < 3 := by
          rw [symmetricThreeCountTernaryReduce word rest]
          exact Nat.mod_lt _ (by decide)
        have reducedCount :
            (symmetricThreeTernaryReduce rest).count word = 2 := by
          omega
        let remainder :=
          ((symmetricThreeTernaryReduce rest).erase word).erase word
        have permutation :
            (symmetricThreeTernaryReduce rest).Perm
              (word :: word :: remainder) := by
          simpa [remainder] using
            symmetricThree_two_copies_perm word
              (symmetricThreeTernaryReduce rest) reducedCount
        have reorder :=
          symmetricThreeDerivesSquareProductPermutation
            identityRepresentative permutation
        have withPrefix :=
          Derives.prepend (symmetricThreeSquare word) reorder
        have cancel :=
          symmetricThreeDerivesCancelThreeSquaresLeft word
            (symmetricThreeSquareProduct identityRepresentative remainder)
        have reduced :
            symmetricThreeTernaryReduce (word :: rest) = remainder := by
          simp [symmetricThreeTernaryReduce, countBound, remainder]
        rw [reduced]
        exact Derives.trans prefixed <|
          Derives.trans
            (by
              simpa [symmetricThreeSquareProduct,
                Word.append_assoc] using withPrefix)
            (by
              simpa [symmetricThreeSquareProduct,
                Word.append_assoc] using cancel)

/-- Square products with the same modulo-three multiplicities derive one
another. -/
theorem symmetricThreeDerivesSquareProductsOfModCounts
    (identityRepresentative : Word Nat)
    (first second : List (Word Nat))
    (counts : ∀ word, first.count word % 3 = second.count word % 3) :
    Derives symmetricThreeBasis
      (symmetricThreeSquareProduct identityRepresentative first)
      (symmetricThreeSquareProduct identityRepresentative second) := by
  have firstReduction :=
    symmetricThreeDerivesSquareProductReduction
      identityRepresentative first
  have secondReduction :=
    symmetricThreeDerivesSquareProductReduction
      identityRepresentative second
  have permutation :=
    symmetricThreeTernaryReduce_perm_of_mod_eq counts
  have middle :=
    symmetricThreeDerivesSquareProductPermutation
      identityRepresentative permutation
  exact Derives.trans firstReduction <|
    Derives.trans middle (Derives.symm secondReduction)

end SemigroupBasis.Examples

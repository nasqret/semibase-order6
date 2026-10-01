import SemigroupBasis.CoRoots.Order6SporadicSection12B8Reduction
import SemigroupBasis.CoRoots.S5_107ListDerives
import SemigroupBasis.Examples.ConnectedComponentFourEnvelopeCombinatorics

namespace SemigroupBasis.CoRoots.Order6SporadicSection12

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.Examples

namespace B8Normalization

private abbrev ListDerives :=
  S5_107.ListDerives b8Basis

private def instantiateFiveWords
    (x y z h k : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | 3 => h
  | 4 => k
  | n + 5 => Word.singleton (n + 5)

private theorem basisSandwichSwapEmpty :
    Derives b8Basis
      (Word.mk 0 [1, 2, 0]) (Word.mk 0 [2, 1, 0]) := by
  change Derives b8Basis word_12_3b_empty_left word_12_3b_empty_right
  exact Derives.fromBasis (e := law_12_3b_empty) <| by
    simp [b8Basis]

private theorem basisPowerContractEmpty :
    Derives b8Basis
      (Word.mk 0 [0, 0, 0]) (Word.mk 0 [0, 0]) := by
  change Derives b8Basis word_12_3a_empty_left word_12_3a_empty_right
  exact Derives.fromBasis (e := law_12_3a_empty) <| by
    simp [b8Basis]

private theorem basisPowerContractH :
    Derives b8Basis
      (Word.mk 0 [0, 0, 3, 0]) (Word.mk 0 [0, 3, 0]) := by
  change Derives b8Basis word_12_3a_H_left word_12_3a_H_right
  exact Derives.fromBasis (e := law_12_3a_H) <| by
    simp [b8Basis]

private theorem basisSandwichSwapH :
    Derives b8Basis
      (Word.mk 0 [3, 1, 2, 0]) (Word.mk 0 [3, 2, 1, 0]) := by
  change Derives b8Basis word_12_3b_H_left word_12_3b_H_right
  exact Derives.fromBasis (e := law_12_3b_H) <| by
    simp [b8Basis]

private theorem basisSandwichSwapK :
    Derives b8Basis
      (Word.mk 0 [1, 2, 4, 0]) (Word.mk 0 [2, 1, 4, 0]) := by
  change Derives b8Basis word_12_3b_K_left word_12_3b_K_right
  exact Derives.fromBasis (e := law_12_3b_K) <| by
    simp [b8Basis]

private theorem basisSandwichSwapHK :
    Derives b8Basis
      (Word.mk 0 [3, 1, 2, 4, 0])
      (Word.mk 0 [3, 2, 1, 4, 0]) := by
  change Derives b8Basis word_12_3b_HK_left word_12_3b_HK_right
  exact Derives.fromBasis (e := law_12_3b_HK) <| by
    simp [b8Basis]

private theorem basisLeftCrossingEmpty :
    Derives b8Basis
      (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0]) := by
  change Derives b8Basis
    word_12_3c_left_empty_left word_12_3c_left_empty_right
  exact Derives.fromBasis (e := law_12_3c_left_empty) <| by
    simp [b8Basis]

private theorem basisLeftCrossingH :
    Derives b8Basis
      (Word.mk 0 [3, 1, 0, 1]) (Word.mk 0 [3, 1, 1, 0]) := by
  change Derives b8Basis word_12_3c_left_H_left word_12_3c_left_H_right
  exact Derives.fromBasis (e := law_12_3c_left_H) <| by
    simp [b8Basis]

private theorem basisLeftCrossingK :
    Derives b8Basis
      (Word.mk 0 [1, 4, 0, 1]) (Word.mk 0 [1, 4, 1, 0]) := by
  change Derives b8Basis word_12_3c_left_K_left word_12_3c_left_K_right
  exact Derives.fromBasis (e := law_12_3c_left_K) <| by
    simp [b8Basis]

private theorem basisLeftCrossingHK :
    Derives b8Basis
      (Word.mk 0 [3, 1, 4, 0, 1])
      (Word.mk 0 [3, 1, 4, 1, 0]) := by
  change Derives b8Basis word_12_3c_left_HK_left word_12_3c_left_HK_right
  exact Derives.fromBasis (e := law_12_3c_left_HK) <| by
    simp [b8Basis]

private theorem basisRightCrossingEmpty :
    Derives b8Basis
      (Word.mk 0 [1, 0, 1]) (Word.mk 1 [0, 0, 1]) := by
  change Derives b8Basis
    word_12_3c_right_empty_left word_12_3c_right_empty_right
  exact Derives.fromBasis (e := law_12_3c_right_empty) <| by
    simp [b8Basis]

private theorem basisRightCrossingH :
    Derives b8Basis
      (Word.mk 0 [1, 3, 0, 1]) (Word.mk 1 [0, 3, 0, 1]) := by
  change Derives b8Basis word_12_3c_right_H_left word_12_3c_right_H_right
  exact Derives.fromBasis (e := law_12_3c_right_H) <| by
    simp [b8Basis]

private theorem basisRightCrossingK :
    Derives b8Basis
      (Word.mk 0 [1, 0, 4, 1]) (Word.mk 1 [0, 0, 4, 1]) := by
  change Derives b8Basis word_12_3c_right_K_left word_12_3c_right_K_right
  exact Derives.fromBasis (e := law_12_3c_right_K) <| by
    simp [b8Basis]

private theorem basisRightCrossingHK :
    Derives b8Basis
      (Word.mk 0 [1, 3, 0, 4, 1])
      (Word.mk 1 [0, 3, 0, 4, 1]) := by
  change Derives b8Basis word_12_3c_right_HK_left word_12_3c_right_HK_right
  exact Derives.fromBasis (e := law_12_3c_right_HK) <| by
    simp [b8Basis]

private theorem derivesSandwichSwapEmpty
    (x y z : Word Nat) :
    Derives b8Basis
      (((x ++ y) ++ z) ++ x)
      (((x ++ z) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSandwichSwapEmpty
      (instantiateFiveWords x y z y z)
  simpa [word_12_3b_empty_left, word_12_3b_empty_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesPowerContractEmpty (x : Word Nat) :
    Derives b8Basis
      (((x ++ x) ++ x) ++ x)
      ((x ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisPowerContractEmpty
      (instantiateFiveWords x x x x x)
  simpa [word_12_3a_empty_left, word_12_3a_empty_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesPowerContractH
    (x middle : Word Nat) :
    Derives b8Basis
      ((((x ++ x) ++ x) ++ middle) ++ x)
      (((x ++ x) ++ middle) ++ x) := by
  have substituted :=
    Derives.subst basisPowerContractH
      (instantiateFiveWords x x x middle x)
  simpa [word_12_3a_H_left, word_12_3a_H_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesSandwichSwapH
    (x y z left : Word Nat) :
    Derives b8Basis
      ((((x ++ left) ++ y) ++ z) ++ x)
      ((((x ++ left) ++ z) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSandwichSwapH
      (instantiateFiveWords x y z left z)
  simpa [word_12_3b_H_left, word_12_3b_H_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesSandwichSwapK
    (x y z right : Word Nat) :
    Derives b8Basis
      (((((x ++ y) ++ z) ++ right) ++ x))
      (((((x ++ z) ++ y) ++ right) ++ x)) := by
  have substituted :=
    Derives.subst basisSandwichSwapK
      (instantiateFiveWords x y z y right)
  simpa [word_12_3b_K_left, word_12_3b_K_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesSandwichSwapHK
    (x y z left right : Word Nat) :
    Derives b8Basis
      (((((x ++ left) ++ y) ++ z) ++ right) ++ x)
      (((((x ++ left) ++ z) ++ y) ++ right) ++ x) := by
  have substituted :=
    Derives.subst basisSandwichSwapHK
      (instantiateFiveWords x y z left right)
  simpa [word_12_3b_HK_left, word_12_3b_HK_right,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesLeftCrossingEmpty
    (x y : Word Nat) :
    Derives b8Basis
      (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisLeftCrossingEmpty
      (instantiateFiveWords x y y x y)
  simpa [word_12_3c_left_empty_left,
    word_12_3c_left_empty_right, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesLeftCrossingH
    (x y left : Word Nat) :
    Derives b8Basis
      ((((x ++ left) ++ y) ++ x) ++ y)
      ((((x ++ left) ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisLeftCrossingH
      (instantiateFiveWords x y y left y)
  simpa [word_12_3c_left_H_left,
    word_12_3c_left_H_right, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesLeftCrossingK
    (x y right : Word Nat) :
    Derives b8Basis
      (((((x ++ y) ++ right) ++ x) ++ y))
      (((((x ++ y) ++ right) ++ y) ++ x)) := by
  have substituted :=
    Derives.subst basisLeftCrossingK
      (instantiateFiveWords x y y x right)
  simpa [word_12_3c_left_K_left,
    word_12_3c_left_K_right, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesLeftCrossingHK
    (x y left right : Word Nat) :
    Derives b8Basis
      (((((x ++ left) ++ y) ++ right) ++ x) ++ y)
      (((((x ++ left) ++ y) ++ right) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisLeftCrossingHK
      (instantiateFiveWords x y y left right)
  simpa [word_12_3c_left_HK_left,
    word_12_3c_left_HK_right, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesRightCrossingEmpty
    (x y : Word Nat) :
    Derives b8Basis
      (((x ++ y) ++ x) ++ y)
      (((y ++ x) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisRightCrossingEmpty
      (instantiateFiveWords x y y x y)
  simpa [word_12_3c_right_empty_left,
    word_12_3c_right_empty_right, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesRightCrossingH
    (x y left : Word Nat) :
    Derives b8Basis
      ((((x ++ y) ++ left) ++ x) ++ y)
      ((((y ++ x) ++ left) ++ x) ++ y) := by
  have substituted :=
    Derives.subst basisRightCrossingH
      (instantiateFiveWords x y y left y)
  simpa [word_12_3c_right_H_left,
    word_12_3c_right_H_right, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesRightCrossingK
    (x y right : Word Nat) :
    Derives b8Basis
      (((((x ++ y) ++ x) ++ right) ++ y))
      (((((y ++ x) ++ x) ++ right) ++ y)) := by
  have substituted :=
    Derives.subst basisRightCrossingK
      (instantiateFiveWords x y y x right)
  simpa [word_12_3c_right_K_left,
    word_12_3c_right_K_right, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesRightCrossingHK
    (x y left right : Word Nat) :
    Derives b8Basis
      (((((x ++ y) ++ left) ++ x) ++ right) ++ y)
      (((((y ++ x) ++ left) ++ x) ++ right) ++ y) := by
  have substituted :=
    Derives.subst basisRightCrossingHK
      (instantiateFiveWords x y y left right)
  simpa [word_12_3c_right_HK_left,
    word_12_3c_right_HK_right, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

/-- Contextual (12.3a). The internal context may be empty. -/
theorem listDerivesPowerContract
    (pre suffix : List Nat) (x : Nat) (middle : List Nat) :
    ListDerives
      (pre ++ [x, x, x] ++ middle ++ [x] ++ suffix)
      (pre ++ [x, x] ++ middle ++ [x] ++ suffix) := by
  cases middle with
  | nil =>
      have core := S5_107.ListDerives.ofWord <|
        derivesPowerContractEmpty (Word.singleton x)
      simpa [List.append_assoc, Word.append, Word.singleton] using
        core.context pre suffix
  | cons middleHead middleTail =>
      have core := S5_107.ListDerives.ofWord <|
        derivesPowerContractH
          (Word.singleton x)
          (S5_107.listWordOfCons middleHead middleTail)
      simpa [S5_107.listWordOfCons, List.append_assoc,
        Word.append, Word.singleton] using core.context pre suffix

def capThree (count : Nat) : Nat :=
  if count < 3 then count else 3

def capTwo (count : Nat) : Nat :=
  if count < 2 then count else 2

/-- Contract an adjacent run to length at most three. -/
theorem listDerivesCapRunThree
    (pre suffix : List Nat) (x : Nat) :
    ∀ count,
      ListDerives
        (pre ++ List.replicate count x ++ suffix)
        (pre ++ List.replicate (capThree count) x ++ suffix)
  | 0 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := b8Basis) (pre ++ suffix))
  | 1 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := b8Basis)
          (pre ++ [x] ++ suffix))
  | 2 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := b8Basis)
          (pre ++ [x, x] ++ suffix))
  | 3 => by
      simpa [capThree] using
        (S5_107.ListDerives.refl (basis := b8Basis)
          (pre ++ [x, x, x] ++ suffix))
  | count + 4 => by
      have first :
          ListDerives
            (pre ++ List.replicate (count + 4) x ++ suffix)
            (pre ++ List.replicate (count + 3) x ++ suffix) := by
        simpa [List.replicate_succ, List.append_assoc] using
          listDerivesPowerContract pre
            (List.replicate count x ++ suffix) x []
      exact first.trans
        (listDerivesCapRunThree pre suffix x (count + 3))
termination_by count => count

/-- Contract the prefix run of a matching-endpoint word to length at most
two. The final endpoint is retained throughout. -/
theorem listDerivesCapEndpointPrefix
    (suffix : List Nat) (endpoint : Nat) :
    ∀ count,
      ListDerives
        (List.replicate count endpoint ++ suffix ++ [endpoint])
        (List.replicate (capTwo count) endpoint ++ suffix ++ [endpoint])
  | 0 => by
      simpa [capTwo] using
        (S5_107.ListDerives.refl (basis := b8Basis)
          (suffix ++ [endpoint]))
  | 1 => by
      simpa [capTwo] using
        (S5_107.ListDerives.refl (basis := b8Basis)
          (endpoint :: suffix ++ [endpoint]))
  | 2 => by
      simpa [capTwo] using
        (S5_107.ListDerives.refl (basis := b8Basis)
          (endpoint :: endpoint :: suffix ++ [endpoint]))
  | count + 3 => by
      have first :
          ListDerives
            (List.replicate (count + 3) endpoint ++ suffix ++ [endpoint])
            (List.replicate (count + 2) endpoint ++ suffix ++ [endpoint]) := by
        simpa [List.replicate_succ, List.append_assoc] using
          listDerivesPowerContract [] [] endpoint
            (List.replicate count endpoint ++ suffix)
      exact first.trans
        (listDerivesCapEndpointPrefix suffix endpoint (count + 2))
termination_by count => count

/-- Contextual (12.3b), with both internal contexts allowed to be empty. -/
theorem listDerivesSandwichSwap
    (pre suffix : List Nat) (x y z : Nat)
    (left right : List Nat) :
    ListDerives
      (pre ++ [x] ++ left ++ [y, z] ++ right ++ [x] ++ suffix)
      (pre ++ [x] ++ left ++ [z, y] ++ right ++ [x] ++ suffix) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have core := S5_107.ListDerives.ofWord <|
            derivesSandwichSwapEmpty
              (Word.singleton x) (Word.singleton y) (Word.singleton z)
          simpa [List.append_assoc, Word.append, Word.singleton] using
            core.context pre suffix
      | cons rightHead rightTail =>
          have core := S5_107.ListDerives.ofWord <|
            derivesSandwichSwapK
              (Word.singleton x) (Word.singleton y) (Word.singleton z)
              (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have core := S5_107.ListDerives.ofWord <|
            derivesSandwichSwapH
              (Word.singleton x) (Word.singleton y) (Word.singleton z)
              (S5_107.listWordOfCons leftHead leftTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix
      | cons rightHead rightTail =>
          have core := S5_107.ListDerives.ofWord <|
            derivesSandwichSwapHK
              (Word.singleton x) (Word.singleton y) (Word.singleton z)
              (S5_107.listWordOfCons leftHead leftTail)
              (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix

/-- Contextual left identity in (12.3c), again including all four empty
boundary cases. -/
theorem listDerivesLeftCrossingSwap
    (pre suffix : List Nat) (x y : Nat)
    (left right : List Nat) :
    ListDerives
      (pre ++ [x] ++ left ++ [y] ++ right ++ [x, y] ++ suffix)
      (pre ++ [x] ++ left ++ [y] ++ right ++ [y, x] ++ suffix) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have core := S5_107.ListDerives.ofWord <|
            derivesLeftCrossingEmpty
              (Word.singleton x) (Word.singleton y)
          simpa [List.append_assoc, Word.append, Word.singleton] using
            core.context pre suffix
      | cons rightHead rightTail =>
          have core := S5_107.ListDerives.ofWord <|
            derivesLeftCrossingK
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have core := S5_107.ListDerives.ofWord <|
            derivesLeftCrossingH
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons leftHead leftTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix
      | cons rightHead rightTail =>
          have core := S5_107.ListDerives.ofWord <|
            derivesLeftCrossingHK
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons leftHead leftTail)
              (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix

/-- Contextual right identity in (12.3c). -/
theorem listDerivesRightCrossingSwap
    (pre suffix : List Nat) (x y : Nat)
    (left right : List Nat) :
    ListDerives
      (pre ++ [x, y] ++ left ++ [x] ++ right ++ [y] ++ suffix)
      (pre ++ [y, x] ++ left ++ [x] ++ right ++ [y] ++ suffix) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          have core := S5_107.ListDerives.ofWord <|
            derivesRightCrossingEmpty
              (Word.singleton x) (Word.singleton y)
          simpa [List.append_assoc, Word.append, Word.singleton] using
            core.context pre suffix
      | cons rightHead rightTail =>
          have core := S5_107.ListDerives.ofWord <|
            derivesRightCrossingK
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix
  | cons leftHead leftTail =>
      cases right with
      | nil =>
          have core := S5_107.ListDerives.ofWord <|
            derivesRightCrossingH
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons leftHead leftTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix
      | cons rightHead rightTail =>
          have core := S5_107.ListDerives.ofWord <|
            derivesRightCrossingHK
              (Word.singleton x) (Word.singleton y)
              (S5_107.listWordOfCons leftHead leftTail)
              (S5_107.listWordOfCons rightHead rightTail)
          simpa [S5_107.listWordOfCons, List.append_assoc,
            Word.append, Word.singleton] using core.context pre suffix

/-- Any permutation of a selected interior segment is derivable between
matching endpoints. -/
theorem listDerivesInteriorPermutation
    (pre suffix : List Nat) (endpoint : Nat) (fixed : List Nat)
    {left right : List Nat} (permutation : left.Perm right) :
    ListDerives
      (pre ++ [endpoint] ++ fixed ++ left ++ [endpoint] ++ suffix)
      (pre ++ [endpoint] ++ fixed ++ right ++ [endpoint] ++ suffix) := by
  induction permutation generalizing fixed with
  | nil =>
      exact S5_107.ListDerives.refl _
  | cons head _ ih =>
      simpa [List.append_assoc] using ih (fixed ++ [head])
  | swap first second rest =>
      simpa [List.append_assoc] using
        listDerivesSandwichSwap pre suffix endpoint second first
          fixed rest
  | trans _ _ ihFirst ihSecond =>
      exact (ihFirst fixed).trans (ihSecond fixed)

private theorem perm_one_to_end (letter : Nat) :
    ∀ letters : List Nat,
      (letter :: letters).Perm (letters ++ [letter])
  | [] => List.Perm.refl _
  | head :: tail =>
      (List.Perm.swap head letter tail).trans <|
        List.Perm.cons head (perm_one_to_end letter tail)

private theorem perm_two_to_edges
    (letter : Nat) (letters : List Nat)
    (twice : 2 ≤ letters.count letter) :
    letters.Perm
      (letter :: (letters.erase letter).erase letter ++ [letter]) := by
  have firstMember : letter ∈ letters :=
    List.count_pos_iff.mp (by omega)
  have erasedCount :
      (letters.erase letter).count letter = letters.count letter - 1 := by
    rw [List.count_erase_self]
  have secondMember : letter ∈ letters.erase letter :=
    List.count_pos_iff.mp (by rw [erasedCount]; omega)
  have first := List.perm_cons_erase firstMember
  have second := List.perm_cons_erase secondMember
  exact first.trans <| (List.Perm.cons letter second).trans <|
    List.Perm.cons letter <| perm_one_to_end letter _

/-- Switch matching endpoints from `oldEndpoint` to a distinct letter that
occurs at least twice in the old interior. -/
theorem listDerivesEndpointSwitch
    (oldEndpoint newEndpoint : Nat) (interior : List Nat)
    (different : oldEndpoint ≠ newEndpoint)
    (repeated : 2 ≤ interior.count newEndpoint) :
    ListDerives
      (oldEndpoint :: interior ++ [oldEndpoint])
      (newEndpoint :: oldEndpoint ::
        (interior.erase newEndpoint).erase newEndpoint ++
          [oldEndpoint, newEndpoint]) := by
  let remainder := (interior.erase newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm (newEndpoint :: remainder ++ [newEndpoint]) :=
    perm_two_to_edges newEndpoint interior repeated
  have first :=
    listDerivesInteriorPermutation [] [] oldEndpoint [] arrange
  have second :=
    (listDerivesLeftCrossingSwap [] []
      oldEndpoint newEndpoint [] remainder).symm
  have third :=
    listDerivesRightCrossingSwap [] []
      oldEndpoint newEndpoint remainder []
  have first' :
      ListDerives
        (oldEndpoint :: interior ++ [oldEndpoint])
        (oldEndpoint :: newEndpoint :: remainder ++
          [newEndpoint, oldEndpoint]) := by
    simpa [List.append_assoc] using first
  have second' :
      ListDerives
        (oldEndpoint :: newEndpoint :: remainder ++
          [newEndpoint, oldEndpoint])
        (oldEndpoint :: newEndpoint :: remainder ++
          [oldEndpoint, newEndpoint]) := by
    simpa [List.append_assoc] using second
  have third' :
      ListDerives
        (oldEndpoint :: newEndpoint :: remainder ++
          [oldEndpoint, newEndpoint])
        (newEndpoint :: oldEndpoint :: remainder ++
          [oldEndpoint, newEndpoint]) := by
    simpa [List.append_assoc] using third
  simpa [remainder] using first'.trans (second'.trans third')

/-- Endpoint switching only rearranges occurrences.  Keeping this certificate
separate from derivability makes the later canonical assembly independent of
the particular three-step rewrite used above. -/
theorem listDerivesEndpointSwitch_perm
    (oldEndpoint newEndpoint : Nat) (interior : List Nat)
    (_different : oldEndpoint ≠ newEndpoint)
    (repeated : 2 ≤ interior.count newEndpoint) :
    (oldEndpoint :: interior ++ [oldEndpoint]).Perm
      (newEndpoint :: oldEndpoint ::
        (interior.erase newEndpoint).erase newEndpoint ++
          [oldEndpoint, newEndpoint]) := by
  have arrange := perm_two_to_edges newEndpoint interior repeated
  rw [List.perm_iff_count]
  intro tested
  have counts := (List.perm_iff_count.mp arrange) tested
  simp only [List.count_cons, List.count_append, List.count_nil] at counts ⊢
  omega

private theorem supportConnected_of_connected
    {word : Word Nat} (connected : Connected word) :
    ConnectedComponentSupportConnected word.toList := by
  intro left right shape leftNonempty rightNonempty
  apply Classical.byContradiction
  intro disjoint
  obtain ⟨leftHead, leftTail, leftShape⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rightShape⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  subst left
  subst right
  apply connected.2
  let leftWord : Word Nat := ⟨leftHead, leftTail⟩
  let rightWord : Word Nat := ⟨rightHead, rightTail⟩
  refine ⟨leftWord, rightWord, ?_, ?_⟩
  · apply Word.toList_injective
    exact shape
  · intro letter leftMember rightMember
    apply disjoint
    exact ⟨letter, leftMember, rightMember⟩

private theorem exists_last_occurrence
    {tested : Nat} :
    ∀ {letters : List Nat}, tested ∈ letters →
      ∃ before after,
        letters = before ++ tested :: after ∧ tested ∉ after
  | [], member => by simp at member
  | head :: tail, member => by
      by_cases later : tested ∈ tail
      · rcases exists_last_occurrence later with
          ⟨before, after, shape, absent⟩
        exact ⟨head :: before, after, by simp [shape], absent⟩
      · have headEq : head = tested := by
          rcases List.mem_cons.mp member with equality | tailMember
          · exact equality.symm
          · exact False.elim (later tailMember)
        subst head
        exact ⟨[], tail, by simp, later⟩

/-- Move the distinguished second endpoint through a linked suffix.  The
suffix-link invariant supplies either an earlier copy of the next letter for
(12.3c), or a crossing letter for (12.3b). -/
theorem listDerivesMoveEndpointToEnd
    (endpoint : Nat) :
    ∀ (interior suffix : List Nat),
      endpoint ∉ suffix →
      ConnectedComponentSuffixLinked
        (endpoint :: interior ++ [endpoint]) suffix →
      ListDerives
        (endpoint :: interior ++ endpoint :: suffix)
        (endpoint :: interior ++ suffix ++ [endpoint])
  | interior, [], _, _ => by
      simpa using
        (S5_107.ListDerives.refl (basis := b8Basis)
          (endpoint :: interior ++ [endpoint]))
  | interior, next :: rest, endpointAbsent, linked => by
      have crossing := linked [] (next :: rest) (by simp) (by simp)
      rcases crossing with
        ⟨letter, frontMember, suffixMember⟩
      have letterNotEndpoint : letter ≠ endpoint := by
        intro equality
        subst letter
        exact endpointAbsent suffixMember
      have letterInInterior : letter ∈ interior := by
        have frontMember' :
            letter ∈ endpoint :: interior ++ [endpoint] := by
          simpa using frontMember
        rcases List.mem_append.mp frontMember' with
          frontMember | finalMember
        · rcases List.mem_cons.mp frontMember with equality | member
          · exact False.elim (letterNotEndpoint equality)
          · exact member
        · have equality : letter = endpoint := by
            simpa using finalMember
          exact False.elim (letterNotEndpoint equality)
      have first :
          ListDerives
            (endpoint :: interior ++ endpoint :: next :: rest)
            (endpoint :: (interior ++ [next]) ++ endpoint :: rest) := by
        rcases List.mem_cons.mp suffixMember with equality | later
        · subst letter
          rcases List.append_of_mem letterInInterior with
            ⟨before, after, interiorShape⟩
          have step :=
            listDerivesLeftCrossingSwap [] rest
              endpoint next before after
          simpa [interiorShape, List.append_assoc] using step
        · rcases List.append_of_mem letterInInterior with
            ⟨before, after, interiorShape⟩
          rcases List.append_of_mem later with
            ⟨rightBefore, rightAfter, restShape⟩
          have step :=
            listDerivesSandwichSwap
              ([endpoint] ++ before) rightAfter
              letter endpoint next after rightBefore
          simpa [interiorShape, restShape, List.append_assoc] using step
      have restAbsent : endpoint ∉ rest := by
        intro member
        exact endpointAbsent (List.Mem.tail next member)
      have nextLinked :
          ConnectedComponentSuffixLinked
            (endpoint :: (interior ++ [next]) ++ [endpoint]) rest := by
        intro left right restShape rightNonempty
        have oldShape :
            next :: rest = (next :: left) ++ right := by
          rw [restShape]
          simp
        rcases linked (next :: left) right oldShape rightNonempty with
          ⟨letter, oldPrefixMember, rightMember⟩
        refine ⟨letter, ?_, rightMember⟩
        simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using
          oldPrefixMember
      have recurse :=
        listDerivesMoveEndpointToEnd endpoint
          (interior ++ [next]) rest restAbsent nextLinked
      exact first.trans <| by
        simpa [List.append_assoc] using recurse
termination_by _ suffix => suffix.length

/-- First stage of Lemma 12.7, with the multiplicity certificate made
explicit: every connected word derives to a permutation with matching initial
and final letters. -/
theorem listDerivesConnectedToMatchingEndpointsWithPermutation
    (word : Word Nat) (connected : Connected word) :
    ∃ interior,
      ListDerives word.toList
        (word.head :: interior ++ [word.head]) ∧
      word.toList.Perm (word.head :: interior ++ [word.head]) := by
  cases word with
  | mk head tail =>
      have tailNonempty : tail ≠ [] := by
        intro empty
        subst tail
        simp [Connected, Word.toList] at connected
      have supportConnected :=
        supportConnected_of_connected connected
      have headInTail : head ∈ tail :=
        connectedComponentSupportConnected_cons_tail
          supportConnected tailNonempty
      rcases exists_last_occurrence headInTail with
        ⟨before, after, tailShape, headAbsent⟩
      have wordShape :
          (Word.mk head tail).toList =
            (head :: before ++ [head]) ++ after := by
        simp [Word.toList, tailShape, List.append_assoc]
      have linked :
          ConnectedComponentSuffixLinked
            (head :: before ++ [head]) after :=
        connectedComponentSuffixLinked_of_connected
          supportConnected wordShape (by simp)
      have moved :=
        listDerivesMoveEndpointToEnd head before after
          headAbsent linked
      refine ⟨before ++ after, ?_, ?_⟩
      · simpa [Word.toList, tailShape, List.append_assoc] using moved
      · rw [List.perm_iff_count]
        intro tested
        simp only [Word.toList, tailShape, List.count_cons,
          List.count_append, List.count_nil]
        omega

/-- First stage of Lemma 12.7 in the derivability-only form used by existing
clients. -/
theorem listDerivesConnectedToMatchingEndpoints
    (word : Word Nat) (connected : Connected word) :
    ∃ interior,
      ListDerives word.toList
        (word.head :: interior ++ [word.head]) := by
  rcases listDerivesConnectedToMatchingEndpointsWithPermutation
      word connected with
    ⟨interior, derivation, _⟩
  exact ⟨interior, derivation⟩

end B8Normalization

end SemigroupBasis.CoRoots.Order6SporadicSection12

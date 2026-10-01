import SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions
import SemigroupBasis.CoRoots.S5_107ListDerives

/-!
# Lee--Zhang Condition 14 derivations

This file formalizes the four contextual consequences (9.2a)--(9.2d) of
Lee--Zhang's six-law system (9.1).  The contexts are lists, so the optional
words `H` and `K` from the paper are represented without introducing empty
semigroup words.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

open SemigroupBasis

private def w (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def xxxx : Word Nat := w 0 [0, 0, 0]
private def xx : Word Nat := w 0 [0]
private def xyyyx : Word Nat := w 0 [1, 1, 1, 0]
private def xyx : Word Nat := w 0 [1, 0]
private def xyxxx : Word Nat := w 0 [1, 0, 0, 0]
private def xxyx : Word Nat := w 0 [0, 1, 0]
private def xyxx : Word Nat := w 0 [1, 0, 0]
private def xyxzx : Word Nat := w 0 [1, 0, 2, 0]
private def xxyzx : Word Nat := w 0 [0, 1, 2, 0]
private def xyxy : Word Nat := w 0 [1, 0, 1]
private def xyyx : Word Nat := w 0 [1, 1, 0]

private def powerLaw : Identity Nat := ⟨xxxx, xx⟩
private def middleCubeLaw : Identity Nat := ⟨xyyyx, xyx⟩
private def rightCubeLaw : Identity Nat := ⟨xyxxx, xyx⟩
private def squareTransferLaw : Identity Nat := ⟨xxyx, xyxx⟩
private def gatherLaw : Identity Nat := ⟨xyxzx, xxyzx⟩
private def swapLaw : Identity Nat := ⟨xyxy, xyyx⟩

private def directBasis : List (Identity Nat) :=
  [powerLaw, middleCubeLaw, rightCubeLaw, squareTransferLaw,
    gatherLaw, swapLaw]

private theorem basis_eq_directBasis : basis = directBasis := by
  decide

private def instantiateThreeWords
    (x y z : Word Nat) : Nat → Word Nat
  | 0 => x
  | 1 => y
  | 2 => z
  | n + 3 => Word.singleton (n + 3)

private theorem basisPower :
    Derives basis powerLaw.lhs powerLaw.rhs :=
  Derives.fromBasis (e := powerLaw) <| by
    rw [basis_eq_directBasis]
    simp [directBasis]

private theorem basisMiddleCube :
    Derives basis middleCubeLaw.lhs middleCubeLaw.rhs :=
  Derives.fromBasis (e := middleCubeLaw) <| by
    rw [basis_eq_directBasis]
    simp [directBasis]

private theorem basisRightCube :
    Derives basis rightCubeLaw.lhs rightCubeLaw.rhs :=
  Derives.fromBasis (e := rightCubeLaw) <| by
    rw [basis_eq_directBasis]
    simp [directBasis]

private theorem basisSquareTransfer :
    Derives basis squareTransferLaw.lhs squareTransferLaw.rhs :=
  Derives.fromBasis (e := squareTransferLaw) <| by
    rw [basis_eq_directBasis]
    simp [directBasis]

private theorem basisGather :
    Derives basis gatherLaw.lhs gatherLaw.rhs :=
  Derives.fromBasis (e := gatherLaw) <| by
    rw [basis_eq_directBasis]
    simp [directBasis]

private theorem basisSwap :
    Derives basis swapLaw.lhs swapLaw.rhs :=
  Derives.fromBasis (e := swapLaw) <| by
    rw [basis_eq_directBasis]
    simp [directBasis]

private theorem derivesPower (x : Word Nat) :
    Derives basis (((x ++ x) ++ x) ++ x) (x ++ x) := by
  have substituted :=
    Derives.subst basisPower (instantiateThreeWords x x x)
  simpa [powerLaw, xxxx, xx, w, instantiateThreeWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derivesMiddleCube (x y : Word Nat) :
    Derives basis ((((x ++ y) ++ y) ++ y) ++ x)
      ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisMiddleCube (instantiateThreeWords x y y)
  simpa [middleCubeLaw, xyyyx, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesRightCube (x y : Word Nat) :
    Derives basis (((((x ++ y) ++ x) ++ x) ++ x))
      ((x ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisRightCube (instantiateThreeWords x y y)
  simpa [rightCubeLaw, xyxxx, xyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesSquareTransfer (x y : Word Nat) :
    Derives basis (((x ++ x) ++ y) ++ x)
      (((x ++ y) ++ x) ++ x) := by
  have substituted :=
    Derives.subst basisSquareTransfer (instantiateThreeWords x y y)
  simpa [squareTransferLaw, xxyx, xyxx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesGather (x y z : Word Nat) :
    Derives basis ((((x ++ y) ++ x) ++ z) ++ x)
      ((((x ++ x) ++ y) ++ z) ++ x) := by
  have substituted :=
    Derives.subst basisGather (instantiateThreeWords x y z)
  simpa [gatherLaw, xyxzx, xxyzx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesSwap (x y : Word Nat) :
    Derives basis (((x ++ y) ++ x) ++ y)
      (((x ++ y) ++ y) ++ x) := by
  have substituted :=
    Derives.subst basisSwap (instantiateThreeWords x y y)
  simpa [swapLaw, xyxy, xyyx, w, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using
      substituted

private theorem derivesTransCongr
    {firstSource firstTarget secondSource secondTarget : Word Nat}
    (first : Derives basis firstSource firstTarget)
    (second : Derives basis secondSource secondTarget)
    (middle : firstTarget = secondSource) :
    Derives basis firstSource secondTarget := by
  subst secondSource
  exact first.trans second

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

private theorem listDerivesTransCongr
    {firstSource firstTarget secondSource secondTarget : List Nat}
    (first : ListDerives firstSource firstTarget)
    (second : ListDerives secondSource secondTarget)
    (middle : firstTarget = secondSource) :
    ListDerives firstSource secondTarget := by
  subst secondSource
  exact first.trans second

private theorem derivesSquareDeletion_nonempty
    (x h k : Word Nat) :
    Derives basis
      ((((((x ++ h) ++ x) ++ x) ++ k) ++ x))
      (((x ++ h) ++ k) ++ x) := by
  have first := derivesGather x h (x ++ k)
  have second := derivesGather x (x ++ h) k
  have third := derivesSquareTransfer x ((x ++ h) ++ k)
  have fourth := derivesSquareTransfer x ((h ++ k) ++ x)
  have fifth := derivesRightCube x (h ++ k)
  have firstSecond :=
    derivesTransCongr first second (by simp [Word.append_assoc])
  have throughThird :=
    derivesTransCongr firstSecond third (by simp [Word.append_assoc])
  have throughFourth :=
    derivesTransCongr throughThird fourth (by simp [Word.append_assoc])
  have throughFifth :=
    derivesTransCongr throughFourth fifth (by simp [Word.append_assoc])
  simpa [Word.append_assoc] using throughFifth

private theorem derivesSquareDeletion_leftEmpty
    (x k : Word Nat) :
    Derives basis (((((x ++ x) ++ x) ++ k) ++ x))
      ((x ++ k) ++ x) := by
  have first := derivesSquareTransfer x (x ++ k)
  have second := derivesSquareTransfer x (k ++ x)
  have third := derivesRightCube x k
  have firstSecond :=
    derivesTransCongr first second (by simp [Word.append_assoc])
  have throughThird :=
    derivesTransCongr firstSecond third (by simp [Word.append_assoc])
  simpa [Word.append_assoc] using throughThird

private theorem derivesSquareDeletion_rightEmpty
    (x h : Word Nat) :
    Derives basis ((((x ++ h) ++ x) ++ x) ++ x)
      ((x ++ h) ++ x) := by
  simpa [Word.append_assoc] using derivesRightCube x h

/-- Lee--Zhang (9.2a): `x H x^2 K x = x H K x`, including every
combination in which either optional context is empty. -/
theorem listDerivesContextSquareDeletion
    (x : Nat) (h k : List Nat) :
    ListDerives
      ([x] ++ h ++ [x, x] ++ k ++ [x])
      ([x] ++ h ++ k ++ [x]) := by
  cases h with
  | nil =>
      cases k with
      | nil =>
          simpa [Word.singleton, Word.append, List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis) (derivesPower (Word.singleton x)))
      | cons kHead kTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesSquareDeletion_leftEmpty
                (Word.singleton x) (listWordOfCons kHead kTail)))
  | cons hHead hTail =>
      cases k with
      | nil =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesSquareDeletion_rightEmpty
                (Word.singleton x) (listWordOfCons hHead hTail)))
      | cons kHead kTail =>
          simpa [listWordOfCons, Word.singleton, Word.append,
            List.append_assoc] using
            (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (basis := basis)
              (derivesSquareDeletion_nonempty
                (Word.singleton x)
                (listWordOfCons hHead hTail)
                (listWordOfCons kHead kTail)))

/-- Block form of Lee--Zhang (9.2b). The repeated `block` is a nonempty
semigroup word, while `H` and `K` remain optional list contexts. -/
theorem listDerivesContextCubeDeletionBlock
    (x : Nat) (h k : List Nat) (block : Word Nat) :
    ListDerives
      ([x] ++ h ++ block.toList ++ block.toList ++ block.toList ++
        k ++ [x])
      ([x] ++ h ++ block.toList ++ k ++ [x]) := by
  have insertLeft :=
    (listDerivesContextSquareDeletion x h
      (block.toList ++ block.toList ++ block.toList ++ k)).symm
  have insertRight :=
    (listDerivesContextSquareDeletion x
      (h ++ [x, x] ++ block.toList ++ block.toList ++ block.toList)
      k).symm
  have contractCore :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (basis := basis)
      (derivesMiddleCube (Word.singleton x) block)).context
        ([x] ++ h ++ [x]) ([x] ++ k ++ [x])
  have removeLeft :=
    listDerivesContextSquareDeletion x h
      (block.toList ++ [x, x] ++ k)
  have removeRight :=
    listDerivesContextSquareDeletion x
      (h ++ block.toList) k
  have firstTwo :=
    listDerivesTransCongr insertLeft insertRight
      (by simp [List.append_assoc])
  have throughCore :=
    listDerivesTransCongr firstTwo contractCore
      (by simp [Word.singleton, Word.toList, Word.append,
        List.append_assoc])
  have throughLeft :=
    listDerivesTransCongr throughCore removeLeft
      (by simp [Word.singleton, Word.toList, Word.append,
        List.append_assoc])
  have throughRight :=
    listDerivesTransCongr throughLeft removeRight
      (by simp [List.append_assoc])
  simpa [Word.singleton, Word.toList, Word.append,
    List.append_assoc] using throughRight

/-- Singleton form of Lee--Zhang (9.2b):
`x H y^3 K x = x H y K x`. -/
theorem listDerivesContextCubeDeletion
    (x y : Nat) (h k : List Nat) :
    ListDerives
      ([x] ++ h ++ [y, y, y] ++ k ++ [x])
      ([x] ++ h ++ [y] ++ k ++ [x]) := by
  simpa [Word.singleton, List.append_assoc] using
    listDerivesContextCubeDeletionBlock x h k (Word.singleton y)

/-- Lee--Zhang (9.2c): `x H y K x y = x H y K y x`. -/
theorem listDerivesContextFinalSwap
    (x y : Nat) (h k : List Nat) :
    ListDerives
      ([x] ++ h ++ [y] ++ k ++ [x, y])
      ([x] ++ h ++ [y] ++ k ++ [y, x]) := by
  have insertY :=
    (listDerivesContextSquareDeletion y k [x]).symm
  have first : ListDerives
      ([x] ++ h ++ [y] ++ k ++ [x, y])
      ([x] ++ h ++ [y] ++ k ++ [y, y, x, y]) :=
    by
      simpa [List.append_assoc] using insertY.prepend ([x] ++ h)
  have insertX :=
    (listDerivesContextSquareDeletion x
      (h ++ [y] ++ k ++ [y]) [y]).symm
  have second := insertX.append [y]
  have swapCore :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (basis := basis)
      (derivesSwap (Word.singleton x) (Word.singleton y))).context
        ([x] ++ h ++ [y] ++ k ++ [y, x]) []
  have removeX :=
    listDerivesContextSquareDeletion x
      (h ++ [y] ++ k ++ [y]) [y, y]
  have contractY :=
    listDerivesContextCubeDeletion x y (h ++ [y] ++ k) []
  have firstTwo :=
    listDerivesTransCongr first second (by simp [List.append_assoc])
  have throughSwap :=
    listDerivesTransCongr firstTwo swapCore
      (by simp [Word.singleton, Word.toList, Word.append,
        List.append_assoc])
  have throughRemoveX :=
    listDerivesTransCongr throughSwap removeX
      (by simp [Word.singleton, Word.toList, Word.append,
        List.append_assoc])
  have throughContractY :=
    listDerivesTransCongr throughRemoveX contractY
      (by simp [List.append_assoc])
  simpa [Word.singleton, Word.toList, Word.append,
    List.append_assoc] using throughContractY

/-- Lee--Zhang (9.2d): `x H y z y K x = x H y^2 z K x`. -/
theorem listDerivesContextGatherRepeat
    (x y z : Nat) (h k : List Nat) :
    ListDerives
      ([x] ++ h ++ [y, z, y] ++ k ++ [x])
      ([x] ++ h ++ [y, y, z] ++ k ++ [x]) := by
  let yz : Word Nat := listWordOfCons y [z]
  have expandBlock :=
    (listDerivesContextCubeDeletionBlock x (h ++ [y]) k yz).symm
  have swapOne :=
    (listDerivesContextFinalSwap y z [] []).context
      ([x] ++ h ++ [y]) ([y, z] ++ k ++ [x])
  have swapTwo :=
    (listDerivesContextFinalSwap y z [] [z, y]).context
      ([x] ++ h ++ [y]) (k ++ [x])
  have swapThree :=
    (listDerivesContextFinalSwap y z [] [z]).context
      ([x] ++ h ++ [y]) ([y] ++ k ++ [x])
  have transfer :=
    (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (basis := basis)
      (derivesSquareTransfer (Word.singleton y)
        (listWordOfCons z [z, z]))).symm.context
          ([x] ++ h ++ [y]) (k ++ [x])
  have contractY :=
    listDerivesContextCubeDeletion x y h ([z, z, z, y] ++ k)
  have contractZ :=
    listDerivesContextCubeDeletion x z (h ++ [y]) ([y] ++ k)
  have targetToSource :
      ListDerives
        ([x] ++ h ++ [y, y, z] ++ k ++ [x])
        ([x] ++ h ++ [y, z, y] ++ k ++ [x]) := by
    have firstTwo :=
      listDerivesTransCongr expandBlock swapOne
        (by simp [yz, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.toList, List.append_assoc])
    have throughSwapTwo :=
      listDerivesTransCongr firstTwo swapTwo
        (by simp [yz, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.toList, List.append_assoc])
    have throughSwapThree :=
      listDerivesTransCongr throughSwapTwo swapThree
        (by simp [List.append_assoc])
    have throughTransfer :=
      listDerivesTransCongr throughSwapThree transfer
        (by simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.singleton, Word.toList, Word.append, List.append_assoc])
    have throughContractY :=
      listDerivesTransCongr throughTransfer contractY
        (by simp [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          Word.singleton, Word.toList, Word.append, List.append_assoc])
    have throughContractZ :=
      listDerivesTransCongr throughContractY contractZ
        (by simp [List.append_assoc])
    simpa [yz, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
      Word.toList, Word.singleton, Word.append, List.append_assoc] using
        throughContractZ
  exact targetToSource.symm

end SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

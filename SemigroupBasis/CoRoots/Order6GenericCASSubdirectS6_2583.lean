import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family
import SemigroupBasis.CoRoots.S5_58
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2583

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2583

open SemigroupBasis
open SemigroupBasis.Examples

namespace Family

abbrev rootSemigroup :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.oppositeTable.semigroup

abbrev rootBasis :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.basis

def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private def instantiateFiveWords
    (u v w t r : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => t
  | 4 => r
  | n + 5 => Word.singleton (n + 5)

private theorem rootLaw0 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law0.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.basis]

private theorem rootLaw1 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law1.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law1.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.basis]

private theorem rootLaw3 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law3.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law3.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.basis]

private theorem rootLaw4 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law4.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law4.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.basis]

private theorem rootLaw5 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law5.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law5.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.basis]

theorem derivesCommutativity (u v : Word Nat) :
    Derives rootBasis (u ++ v) (v ++ u) := by
  have substituted :=
    Derives.subst rootLaw0 (instantiateFiveWords u v v v v)
  simpa [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law0,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton] using
      substituted

theorem derivesPermutation (u v : Word Nat)
    (permutation : u.toList.Perm v.toList) :
    Derives rootBasis u v :=
  SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family.derivesPermutation
    derivesCommutativity u v permutation

theorem derivesQuarticTransfer (u v : Word Nat) :
    Derives rootBasis
      (((u ++ u) ++ u) ++ v)
      (((u ++ v) ++ v) ++ v) := by
  have substituted :=
    Derives.subst rootLaw1 (instantiateFiveWords u v v v v)
  simpa [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law1,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Insert a square of the fifth nonempty factor. -/
theorem derivesDuplicateFifthSquare
    (a b c d u : Word Nat) :
    Derives rootBasis
      ((((a ++ b) ++ c) ++ d) ++ u)
      ((((((a ++ b) ++ c) ++ d) ++ u) ++ u) ++ u) := by
  have substituted :=
    Derives.subst rootLaw5 (instantiateFiveWords a b c d u)
  simpa [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law5,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private def fiveProduct
    (a b c d e : Word Nat) : Word Nat :=
  ((((a ++ b) ++ c) ++ d) ++ e)

private theorem derivesAppendSquareFromFiveArrangement
    (source a b c d marker : Word Nat)
    (arranged : source.toList.Perm
      (fiveProduct a b c d marker).toList) :
    Derives rootBasis source
      ((source ++ marker) ++ marker) := by
  have enter :=
    derivesPermutation source (fiveProduct a b c d marker) arranged
  have duplicate := derivesDuplicateFifthSquare a b c d marker
  have exit :
      Derives rootBasis
        ((fiveProduct a b c d marker ++ marker) ++ marker)
        ((source ++ marker) ++ marker) :=
    derivesPermutation _ _ <| by
      rw [List.perm_iff_count]
      intro z
      have countEq := List.perm_iff_count.mp arranged z
      simp only [Word.toList_append, List.count_append]
      omega
  have duplicated :
      Derives rootBasis
        (fiveProduct a b c d marker)
        ((fiveProduct a b c d marker ++ marker) ++ marker) := by
    simpa [fiveProduct, Word.append_assoc] using duplicate
  exact Derives.trans enter (Derives.trans duplicated exit)

/-- A five-factor product derives to its cube by inserting a square of each
factor in turn. -/
theorem derivesFiveProductCube (a b c d e : Word Nat) :
    Derives rootBasis (fiveProduct a b c d e)
      ((fiveProduct a b c d e ++ fiveProduct a b c d e) ++
        fiveProduct a b c d e) := by
  let source := fiveProduct a b c d e
  have insertA :=
    derivesAppendSquareFromFiveArrangement source b c d e a <| by
      rw [List.perm_iff_count]
      intro z
      simp only [source, fiveProduct, Word.toList_append,
        List.count_append]
      omega
  have insertBBase :=
    derivesAppendSquareFromFiveArrangement source a c d e b <| by
      rw [List.perm_iff_count]
      intro z
      simp only [source, fiveProduct, Word.toList_append,
        List.count_append]
      omega
  have insertCBase :=
    derivesAppendSquareFromFiveArrangement source a b d e c <| by
      rw [List.perm_iff_count]
      intro z
      simp only [source, fiveProduct, Word.toList_append,
        List.count_append]
      omega
  have insertDBase :=
    derivesAppendSquareFromFiveArrangement source a b c e d <| by
      rw [List.perm_iff_count]
      intro z
      simp only [source, fiveProduct, Word.toList_append,
        List.count_append]
      omega
  have insertEBase :=
    derivesAppendSquareFromFiveArrangement source a b c d e <| by
      exact List.Perm.refl _
  have insertB :=
    Derives.appendRight insertBBase (a ++ a)
  have insertC :=
    Derives.appendRight insertCBase ((b ++ b) ++ (a ++ a))
  have insertD :=
    Derives.appendRight insertDBase
      (((c ++ c) ++ (b ++ b)) ++ (a ++ a))
  have insertE :=
    Derives.appendRight insertEBase
      ((((d ++ d) ++ (c ++ c)) ++ (b ++ b)) ++ (a ++ a))
  have insertBStep :
      Derives rootBasis
        ((source ++ a) ++ a)
        ((((source ++ b) ++ b) ++ a) ++ a) := by
    simpa [Word.append_assoc] using insertB
  have insertCStep :
      Derives rootBasis
        ((((source ++ b) ++ b) ++ a) ++ a)
        ((((((source ++ c) ++ c) ++ b) ++ b) ++ a) ++ a) := by
    simpa [Word.append_assoc] using insertC
  have insertDStep :
      Derives rootBasis
        ((((((source ++ c) ++ c) ++ b) ++ b) ++ a) ++ a)
        ((((((((source ++ d) ++ d) ++ c) ++ c) ++ b) ++ b) ++ a) ++ a) := by
    simpa [Word.append_assoc] using insertD
  have insertEStep :
      Derives rootBasis
        ((((((((source ++ d) ++ d) ++ c) ++ c) ++ b) ++ b) ++ a) ++ a)
        ((((((((((source ++ e) ++ e) ++ d) ++ d) ++ c) ++ c) ++ b) ++ b) ++ a) ++ a) := by
    simpa [Word.append_assoc] using insertE
  have allTripled :
      Derives rootBasis source
        ((((((((((source ++ e) ++ e) ++ d) ++ d) ++ c) ++ c) ++ b) ++ b) ++ a) ++ a) := by
    exact Derives.trans insertA <|
      Derives.trans insertBStep <|
      Derives.trans insertCStep <|
      Derives.trans insertDStep insertEStep
  exact allTripled.trans <| derivesPermutation _ _ <| by
    rw [List.perm_iff_count]
    intro z
    simp only [source, fiveProduct, Word.toList_append,
      List.count_append]
    omega

theorem derivesFiveProductFifthPower (a b c d e : Word Nat) :
    Derives rootBasis (fiveProduct a b c d e)
      (((fiveProduct a b c d e ++ fiveProduct a b c d e) ++
          fiveProduct a b c d e) ++
        (fiveProduct a b c d e ++ fiveProduct a b c d e)) := by
  let source := fiveProduct a b c d e
  have cube := derivesFiveProductCube a b c d e
  have addTwo := Derives.appendRight cube (source ++ source)
  exact cube.trans <| by
    simpa [source, Word.append_assoc] using addTwo

/-- The bulk degree-five law, at a whole-word substitution, replaces four
extra copies of the word by an arbitrary square and two extra copies. -/
theorem derivesFifthPowerToSquareCube
    (word marker : Word Nat) :
    Derives rootBasis
      (((word ++ word) ++ word) ++ (word ++ word))
      ((marker ++ marker) ++ ((word ++ word) ++ word)) := by
  have substituted :=
    Derives.subst rootLaw3
      (instantiateFiveWords word marker word word word)
  have applied :
      Derives rootBasis
        (((word ++ word) ++ word) ++ (word ++ word))
        ((((word ++ marker) ++ marker) ++ word) ++ word) := by
    simpa [rootBasis,
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law3,
      instantiateFiveWords, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using substituted
  have arranged :
      Derives rootBasis
        ((((word ++ marker) ++ marker) ++ word) ++ word)
        ((marker ++ marker) ++ ((word ++ word) ++ word)) :=
    derivesPermutation _ _ <| by
      rw [List.perm_iff_count]
      intro z
      simp only [Word.toList_append, List.count_append]
      omega
  exact Derives.trans applied arranged

theorem derivesInsertArbitrarySquareFive
    (marker a b c d e : Word Nat) :
    Derives rootBasis (fiveProduct a b c d e)
      ((marker ++ marker) ++ fiveProduct a b c d e) := by
  let word := fiveProduct a b c d e
  have cube := derivesFiveProductCube a b c d e
  have fifth := derivesFiveProductFifthPower a b c d e
  have bridge := derivesFifthPowerToSquareCube word marker
  have contract := Derives.symm (Derives.prepend (marker ++ marker) cube)
  exact fifth.trans <| bridge.trans <| by
    simpa [word, Word.append_assoc] using contract

/-- Insert an arbitrary square before every word of length at least five. -/
theorem derivesInsertArbitrarySquareLong
    (marker word : Word Nat) (long : 5 ≤ word.toList.length) :
    Derives rootBasis word ((marker ++ marker) ++ word) := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => simp [Word.toList] at long
      | cons second rest =>
          cases rest with
          | nil => simp [Word.toList] at long
          | cons third more =>
              cases more with
              | nil => simp [Word.toList] at long
              | cons fourth remaining =>
                  cases remaining with
                  | nil => simp [Word.toList] at long
                  | cons fifth final =>
                      simpa [fiveProduct, wordOfCons, Word.singleton,
                        Word.append, Word.append_assoc] using
                          derivesInsertArbitrarySquareFive marker
                            (Word.singleton head)
                            (Word.singleton second)
                            (Word.singleton third)
                            (Word.singleton fourth)
                            (wordOfCons fifth final)

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (word : Word Nat)
    (τ σ : Nat → Word Nat) :
    (word.bind τ).bind σ =
      word.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (word : Word Nat) :
    word.bind Word.singleton = word := by
  apply Word.toList_injective
  simp [Word.toList_bind]

theorem derivesContextSquareTransfer
    (a b u v : Word Nat) :
    Derives rootBasis
      ((a ++ b) ++ ((u ++ u) ++ u))
      ((a ++ b) ++ ((u ++ v) ++ v)) := by
  have substituted :=
    Derives.subst rootLaw4 (instantiateFiveWords v a b u u)
  have arranged :
      Derives rootBasis
        ((v ++ v) ++ ((a ++ b) ++ u))
        ((a ++ b) ++ ((u ++ v) ++ v)) :=
    derivesPermutation _ _ <| by
      rw [List.perm_iff_count]
      intro z
      simp only [Word.toList_append, List.count_append]
      omega
  have applied :
      Derives rootBasis
        ((a ++ b) ++ ((u ++ u) ++ u))
        ((v ++ v) ++ ((a ++ b) ++ u)) := by
    simpa [rootBasis,
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.law4,
      instantiateFiveWords, Word.bind, Word.append, Word.singleton,
      Word.append_assoc] using substituted
  exact Derives.trans applied arranged

theorem derivesContextSquareTransferMiddle
    (a b u v : Word Nat) :
    Derives rootBasis
      ((a ++ b) ++ ((u ++ u) ++ u))
      ((a ++ b) ++ ((v ++ u) ++ v)) := by
  exact (derivesContextSquareTransfer a b u v).trans <|
    derivesPermutation _ _ <| by
      rw [List.perm_iff_count]
      intro z
      simp only [Word.toList_append, List.count_append]
      omega

theorem derivesContextSquareTransferLeft
    (a b u v : Word Nat) :
    Derives rootBasis
      ((a ++ b) ++ ((u ++ u) ++ u))
      ((a ++ b) ++ ((v ++ v) ++ u)) := by
  exact (derivesContextSquareTransfer a b u v).trans <|
    derivesPermutation _ _ <| by
      rw [List.perm_iff_count]
      intro z
      simp only [Word.toList_append, List.count_append]
      omega

theorem derivesContextExistingSquare
    (a b u v w : Word Nat) :
    Derives rootBasis
      ((a ++ b) ++ ((u ++ v) ++ w))
      ((a ++ b) ++ ((((u ++ u) ++ u) ++ v) ++ w)) := by
  have enter := derivesPermutation
    ((a ++ b) ++ ((u ++ v) ++ w))
    ((((a ++ b) ++ v) ++ w) ++ u) <| by
      rw [List.perm_iff_count]
      intro z
      simp only [Word.toList_append, List.count_append]
      omega
  have expand := derivesDuplicateFifthSquare a b v w u
  have exit := derivesPermutation
    ((((((a ++ b) ++ v) ++ w) ++ u) ++ u) ++ u)
    ((a ++ b) ++ ((((u ++ u) ++ u) ++ v) ++ w)) <| by
      rw [List.perm_iff_count]
      intro z
      simp only [Word.toList_append, List.count_append]
      omega
  have expanded :
      Derives rootBasis
        ((((a ++ b) ++ v) ++ w) ++ u)
        ((((((a ++ b) ++ v) ++ w) ++ u) ++ u) ++ u) := by
    simpa [Word.append_assoc] using expand
  exact Derives.trans enter (Derives.trans expanded exit)

/-- Replay the established `S5_58` parity derivation behind two fixed
markers. -/
theorem liftS5_58
    {u v : Word Nat}
    (derivation :
      Derives SemigroupBasis.CoRoots.S5_58.basis u v)
    (a b : Word Nat) (σ : Nat → Word Nat) :
    Derives rootBasis
      ((a ++ b) ++ u.bind σ)
      ((a ++ b) ++ v.bind σ) := by
  induction derivation generalizing a b σ with
  | fromBasis member =>
      simp only [SemigroupBasis.CoRoots.S5_58.basis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [SemigroupBasis.CoRoots.S5_58.squareRightLaw,
          SemigroupBasis.CoRoots.S5_58.xxx,
          SemigroupBasis.CoRoots.S5_58.xyy, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
            derivesContextSquareTransfer a b (σ 0) (σ 1)
      · simpa [SemigroupBasis.CoRoots.S5_58.squareMiddleLaw,
          SemigroupBasis.CoRoots.S5_58.xxx,
          SemigroupBasis.CoRoots.S5_58.yxy, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
            derivesContextSquareTransferMiddle a b (σ 0) (σ 1)
      · simpa [SemigroupBasis.CoRoots.S5_58.squareLeftLaw,
          SemigroupBasis.CoRoots.S5_58.xxx,
          SemigroupBasis.CoRoots.S5_58.yyx, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
            derivesContextSquareTransferLeft a b (σ 0) (σ 1)
      · have commute := derivesCommutativity (σ 1) (σ 2)
        simpa [SemigroupBasis.CoRoots.S5_58.suffixCommutationLaw,
          SemigroupBasis.CoRoots.S5_58.xyz,
          SemigroupBasis.CoRoots.S5_58.xzy, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.prepend ((a ++ b) ++ σ 0) commute
      · have commute := derivesCommutativity (σ 0) (σ 1)
        simpa [SemigroupBasis.CoRoots.S5_58.prefixCommutationLaw,
          SemigroupBasis.CoRoots.S5_58.xyz,
          SemigroupBasis.CoRoots.S5_58.yxz, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
            Derives.prepend (a ++ b) <|
              Derives.appendRight commute (σ 2)
      · simpa [SemigroupBasis.CoRoots.S5_58.longInsertionLaw,
          SemigroupBasis.CoRoots.S5_58.xyz,
          SemigroupBasis.CoRoots.S5_58.xxxyz, Word.bind, Word.append,
          Word.singleton, Word.append_assoc] using
            derivesContextExistingSquare a b (σ 0) (σ 1) (σ 2)
  | refl =>
      exact Derives.refl _
  | symm nestedDerivation inductionHypothesis =>
      exact Derives.symm (inductionHypothesis a b σ)
  | trans firstDerivation secondDerivation firstHypothesis secondHypothesis =>
      exact Derives.trans
        (firstHypothesis a b σ) (secondHypothesis a b σ)
  | prepend stem nestedDerivation inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis a (b ++ stem.bind σ) σ
  | appendRight nestedDerivation suffix inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis a b σ) (suffix.bind σ)
  | subst nestedDerivation firstSubstitution inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis a b
          (fun x => (firstSubstitution x).bind σ)

/-- Every pair of words of length at least five with the same coordinate
parity is derivably equal. -/
theorem derivesLongOfParityEq
    (left right : Word Nat)
    (leftLong : 5 ≤ left.toList.length)
    (rightLong : 5 ≤ right.toList.length)
    (parity : ∀ z,
      left.toList.count z % 2 = right.toList.count z % 2) :
    Derives rootBasis left right := by
  let marker := Word.singleton 0
  have insertLeft :=
    derivesInsertArbitrarySquareLong marker left leftLong
  have insertRight :=
    derivesInsertArbitrarySquareLong marker right rightLong
  have parityDerivation :=
    SemigroupBasis.CoRoots.S5_58.derivesLongOfParityEq
      left right (by omega) (by omega) parity
  have lifted := liftS5_58 parityDerivation marker marker Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact insertLeft.trans <| lifted.trans (Derives.symm insertRight)

private theorem count_pair_eq_length
    (a b : Nat) (ab : a ≠ b) :
    ∀ xs : List Nat,
      (∀ z, z ∈ xs → z = a ∨ z = b) →
      xs.count a + xs.count b = xs.length
  | [], _ => by simp
  | x :: xs, members => by
      have head := members x (by simp)
      have tailMembers :
          ∀ z, z ∈ xs → z = a ∨ z = b := by
        intro z member
        exact members z (by simp [member])
      have ih := count_pair_eq_length a b ab xs tailMembers
      rcases head with rfl | rfl
      · rw [List.count_cons_self,
          List.count_cons_of_ne ab, List.length_cons]
        omega
      · rw [List.count_cons_of_ne (Ne.symm ab),
          List.count_cons_self, List.length_cons]
        omega

private theorem pair_perm_of_counts
    {a b : Nat} (ab : a ≠ b) {xs ys : List Nat}
    (xsMembers : ∀ z, z ∈ xs → z = a ∨ z = b)
    (ysMembers : ∀ z, z ∈ ys → z = a ∨ z = b)
    (countA : xs.count a = ys.count a)
    (countB : xs.count b = ys.count b) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro z
  by_cases za : z = a
  · subst z
    exact countA
  · by_cases zb : z = b
    · subst z
      exact countB
    · have xsZero : xs.count z = 0 :=
        List.count_eq_zero.mpr <| by
          intro member
          rcases xsMembers z member with equal | equal
          · exact za equal
          · exact zb equal
      have ysZero : ys.count z = 0 :=
        List.count_eq_zero.mpr <| by
          intro member
          rcases ysMembers z member with equal | equal
          · exact za equal
          · exact zb equal
      rw [xsZero, ysZero]

private theorem three_copies_perm (z : Nat) (xs : List Nat)
    (countThree : xs.count z = 3) :
    xs.Perm
      (z :: z :: z :: (((xs.erase z).erase z).erase z)) := by
  have firstPresent : z ∈ xs :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase firstPresent
  have countTwo : (xs.erase z).count z = 2 := by
    rw [List.count_erase_self]
    omega
  have secondPresent : z ∈ xs.erase z :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase secondPresent
  have countOne : ((xs.erase z).erase z).count z = 1 := by
    rw [List.count_erase_self]
    omega
  have thirdPresent : z ∈ (xs.erase z).erase z :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons z <|
    second.trans <| List.Perm.cons z
      (List.perm_cons_erase thirdPresent)

private theorem all_eq_of_count_eq_length (z : Nat) :
    ∀ xs : List Nat,
      xs.count z = xs.length →
        ∀ x, x ∈ xs → x = z
  | [], _, x, member => by simp at member
  | y :: ys, equal, x, member => by
      have yEqual : y = z := by
        by_cases equalHead : y = z
        · exact equalHead
        · rw [List.count_cons_of_ne equalHead, List.length_cons] at equal
          have bound := List.count_le_length (a := z) (l := ys)
          omega
      subst y
      have tailEqual : ys.count z = ys.length := by
        rw [List.count_cons_self, List.length_cons] at equal
        omega
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact all_eq_of_count_eq_length z ys tailEqual x member

private theorem count_eq_length_of_all_eq
    (z : Nat) : ∀ xs : List Nat,
      (∀ x, x ∈ xs → x = z) → xs.count z = xs.length
  | [], _ => by simp
  | x :: xs, allEqual => by
      have headEqual := allEqual x (by simp)
      subst x
      have tailEqual : ∀ y, y ∈ xs → y = z := by
        intro y member
        exact allEqual y (by simp [member])
      rw [List.count_cons_self, List.length_cons,
        count_eq_length_of_all_eq z xs tailEqual]

private theorem lengthFour_perm_threeOne
    (xs : List Nat) (z : Nat)
    (lengthFour : xs.length = 4)
    (countThree : xs.count z = 3) :
    ∃ y, z ≠ y ∧ xs.Perm [z, z, z, y] := by
  let remainder := (((xs.erase z).erase z).erase z)
  have permutation : xs.Perm (z :: z :: z :: remainder) := by
    simpa [remainder] using three_copies_perm z xs countThree
  have remainderLength : remainder.length = 1 := by
    have lengths := permutation.length_eq
    simp [lengthFour] at lengths
    omega
  obtain ⟨y, remainderEq⟩ : ∃ y, remainder = [y] := by
    cases remainderShape : remainder with
    | nil =>
        rw [remainderShape] at remainderLength
        simp at remainderLength
    | cons y ys =>
        cases tailShape : ys with
        | nil =>
            exact ⟨y, by simpa [tailShape] using remainderShape⟩
        | cons q qs =>
            rw [remainderShape, tailShape] at remainderLength
            simp at remainderLength
  rw [remainderEq] at permutation
  have different : z ≠ y := by
    intro equal
    subst y
    have countEquality := List.perm_iff_count.mp permutation z
    rw [countThree] at countEquality
    simp at countEquality
  exact ⟨y, different, by simpa using permutation⟩

private theorem derivesQuarticThreeOne
    (left right : Word Nat) (z : Nat)
    (leftFour : left.toList.length = 4)
    (rightFour : right.toList.length = 4)
    (support : ∀ q, q ∈ left.toList ↔ q ∈ right.toList)
    (leftThree : left.toList.count z = 3)
    (rightOne : right.toList.count z = 1) :
    Derives rootBasis left right := by
  obtain ⟨y, different, leftPerm⟩ :=
    lengthFour_perm_threeOne left.toList z leftFour leftThree
  have leftMembers :
      ∀ q, q ∈ left.toList → q = z ∨ q = y := by
    intro q member
    have canonical := leftPerm.mem_iff.mp member
    simpa [or_assoc, or_left_comm, or_comm] using canonical
  have rightMembers :
      ∀ q, q ∈ right.toList → q = z ∨ q = y := by
    intro q member
    exact leftMembers q ((support q).mpr member)
  have rightCountY : right.toList.count y = 3 := by
    have sum :=
      count_pair_eq_length z y different right.toList rightMembers
    rw [rightOne, rightFour] at sum
    omega
  have rightPerm : right.toList.Perm [y, y, y, z] :=
    pair_perm_of_counts different rightMembers
      (by
        intro q member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl rfl)
      (by simpa [different, Ne.symm different] using rightOne)
      (by simpa [different, Ne.symm different] using rightCountY)
  have enter :
      Derives rootBasis left (wordOfCons z [z, z, y]) :=
    derivesPermutation _ _ <| by
      simpa [wordOfCons, Word.toList] using leftPerm
  have transfer :=
    derivesQuarticTransfer (Word.singleton z) (Word.singleton y)
  have arrange :
      Derives rootBasis
        (wordOfCons z [y, y, y])
        (wordOfCons y [y, y, z]) :=
    derivesPermutation _ _ <| by
      rw [List.perm_iff_count]
      intro q
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega
  have exit :
      Derives rootBasis (wordOfCons y [y, y, z]) right :=
    Derives.symm <| derivesPermutation _ _ <| by
      simpa [wordOfCons, Word.toList] using rightPerm
  have transferred :
      Derives rootBasis
        (wordOfCons z [z, z, y])
        (wordOfCons z [y, y, y]) := by
    simpa [wordOfCons, Word.singleton, Word.append,
      Word.append_assoc] using transfer
  exact Derives.trans enter <|
    Derives.trans transferred <| Derives.trans arrange exit

/-- Degree-four words are classified by support and coordinate parity. -/
theorem derivesLengthFourSupportParity
    (left right : Word Nat)
    (leftFour : left.toList.length = 4)
    (rightFour : right.toList.length = 4)
    (support : ∀ z, z ∈ left.toList ↔ z ∈ right.toList)
    (parity : ∀ z,
      left.toList.count z % 2 = right.toList.count z % 2) :
    Derives rootBasis left right := by
  by_cases counts :
      ∀ z, left.toList.count z = right.toList.count z
  · exact derivesPermutation left right <|
      List.perm_iff_count.mpr counts
  · have differing :
        ∃ z, left.toList.count z ≠ right.toList.count z := by
      apply Classical.byContradiction
      intro noWitness
      apply counts
      intro z
      by_cases equalCount :
          left.toList.count z = right.toList.count z
      · exact equalCount
      · exact False.elim (noWitness ⟨z, equalCount⟩)
    obtain ⟨z, differentCount⟩ := differing
    have zeroIff :
        left.toList.count z = 0 ↔ right.toList.count z = 0 := by
      rw [List.count_eq_zero, List.count_eq_zero]
      exact not_congr (support z)
    have leftPositive : 0 < left.toList.count z := by
      apply Nat.pos_of_ne_zero
      intro leftZero
      have rightZero := zeroIff.mp leftZero
      exact differentCount (by omega)
    have rightPositive : 0 < right.toList.count z := by
      apply Nat.pos_of_ne_zero
      intro rightZero
      have leftZero := zeroIff.mpr rightZero
      exact differentCount (by omega)
    have leftBound :=
      List.count_le_length (a := z) (l := left.toList)
    have rightBound :=
      List.count_le_length (a := z) (l := right.toList)
    have leftNotFour : left.toList.count z ≠ 4 := by
      intro leftFourCount
      have leftAll :=
        all_eq_of_count_eq_length z left.toList (by
          rw [leftFour]
          exact leftFourCount)
      have rightAll : ∀ q, q ∈ right.toList → q = z := by
        intro q member
        exact leftAll q ((support q).mpr member)
      have rightFourCount :=
        count_eq_length_of_all_eq z right.toList rightAll
      rw [rightFour] at rightFourCount
      exact differentCount (by omega)
    have rightNotFour : right.toList.count z ≠ 4 := by
      intro rightFourCount
      have rightAll :=
        all_eq_of_count_eq_length z right.toList (by
          rw [rightFour]
          exact rightFourCount)
      have leftAll : ∀ q, q ∈ left.toList → q = z := by
        intro q member
        exact rightAll q ((support q).mp member)
      have leftFourCount :=
        count_eq_length_of_all_eq z left.toList leftAll
      rw [leftFour] at leftFourCount
      exact differentCount (by omega)
    have countCases :
        (left.toList.count z = 3 ∧ right.toList.count z = 1) ∨
          (left.toList.count z = 1 ∧
            right.toList.count z = 3) := by
      have parityAtZ := parity z
      omega
    rcases countCases with ⟨leftThree, rightOne⟩ |
        ⟨leftOne, rightThree⟩
    · exact derivesQuarticThreeOne left right z
        leftFour rightFour support leftThree rightOne
    · exact Derives.symm <| derivesQuarticThreeOne right left z
        rightFour leftFour (fun q => (support q).symm)
        rightThree leftOne

/-- Factor validity is sufficient for a root derivation in every S5_194
length stratum. -/
theorem derivesOfFactorValidity
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_194.table.semigroup) :
    Derives rootBasis identity.lhs identity.rhs := by
  have cyclicValid : identity.SatisfiedBy cyclicTwo.semigroup := by
    rw [← SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family.catalogueS2_2_table_eq_cyclicTwo]
    exact leftValid
  have parity := cyclicValid_parity_eq identity cyclicValid
  cases SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family.s5_194Shape_of_valid
      identity rightValid with
  | one _ _ counts =>
      exact derivesPermutation identity.lhs identity.rhs <|
        List.perm_iff_count.mpr counts
  | two _ _ counts =>
      exact derivesPermutation identity.lhs identity.rhs <|
        List.perm_iff_count.mpr counts
  | three _ _ counts =>
      exact derivesPermutation identity.lhs identity.rhs <|
        List.perm_iff_count.mpr counts
  | four leftFour rightFour support =>
      exact derivesLengthFourSupportParity identity.lhs identity.rhs
        leftFour rightFour support parity
  | long leftLong rightLong =>
      exact derivesLongOfParityEq identity.lhs identity.rhs
        leftLong rightLong parity

end Family

abbrev rootSemigroup :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.oppositeTable.semigroup

abbrev rootBasis :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.basis

abbrev leftFactor :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2583.leftFactor

abbrev rightFactor :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2583.rightFactor

private abbrev factorPair :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_2583.subdirectPair

private theorem leftFactorModels : Models leftFactor rootBasis := by
  intro identity member
  exact factorPair.left.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.models
      identity member)

private theorem rightFactorModels : Models rightFactor rootBasis := by
  intro identity member
  exact factorPair.right.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2583.models
      identity member)

/-- Exact unconditional basis endpoint for the mixed generic-CAS root
`S6_2583`. -/
theorem basisFor : BasisFor rootSemigroup rootBasis :=
  (IntersectionBasis.mk leftFactorModels rightFactorModels
    Family.derivesOfFactorValidity).basisFor factorPair

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2583

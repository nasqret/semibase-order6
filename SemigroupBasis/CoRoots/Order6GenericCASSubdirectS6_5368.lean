import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family
import SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5368

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5368

open SemigroupBasis
open SemigroupBasis.Examples

namespace Family

abbrev rootSemigroup :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup

abbrev rootBasis :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis

def wordOfCons (head : Nat) (tail : List Nat) : Word Nat :=
  ⟨head, tail⟩

private theorem perm_append_comm (left right : List Nat) :
    (left ++ right).Perm (right ++ left) := by
  rw [List.perm_iff_count]
  intro letter
  simp only [List.count_append]
  omega

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
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law0.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law0.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis]

private theorem rootLaw2 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law2.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law2.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis]

private theorem rootLaw3 :
    Derives rootBasis
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law3.lhs
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law3.rhs := by
  apply Derives.fromBasis
  simp [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis]

theorem derivesCommutativity (u v : Word Nat) :
    Derives rootBasis (u ++ v) (v ++ u) := by
  have substituted :=
    Derives.subst rootLaw0 (instantiateFiveWords u v v v v)
  simpa [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law0,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton] using
      substituted

theorem derivesPermutation (u v : Word Nat)
    (permutation : u.toList.Perm v.toList) :
    Derives rootBasis u v :=
  SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family.derivesPermutation
    derivesCommutativity u v permutation

/-- The degree-four law transfers the repeated variable while retaining the
two contextual factors. -/
theorem derivesMultiplicityTransfer (u v t : Word Nat) :
    Derives rootBasis
      (((u ++ v) ++ v) ++ t)
      (((u ++ u) ++ v) ++ t) := by
  have substituted :=
    Derives.subst (Derives.symm rootLaw2)
      (instantiateFiveWords u v t t t)
  simpa [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law2,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

/-- Duplicate the fifth nonempty factor. -/
theorem derivesDuplicateFifth
    (a b c d u : Word Nat) :
    Derives rootBasis
      ((((a ++ b) ++ c) ++ d) ++ u)
      (((((a ++ b) ++ c) ++ d) ++ u) ++ u) := by
  have substituted :=
    Derives.subst rootLaw3 (instantiateFiveWords a b c d u)
  simpa [rootBasis,
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.law3,
    instantiateFiveWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

private theorem derivesAppendMember
    (word : Word Nat) (marker : Nat)
    (long : 5 ≤ word.toList.length)
    (present : marker ∈ word.toList) :
    Derives rootBasis word (word ++ Word.singleton marker) := by
  have erasedLength := List.length_erase_of_mem present
  cases erased : word.toList.erase marker with
  | nil =>
      rw [erased] at erasedLength
      simp at erasedLength
      omega
  | cons a rest =>
      cases rest with
      | nil =>
          rw [erased] at erasedLength
          simp at erasedLength
          omega
      | cons b rest =>
          cases rest with
          | nil =>
              rw [erased] at erasedLength
              simp at erasedLength
              omega
          | cons c rest =>
              cases rest with
              | nil =>
                  rw [erased] at erasedLength
                  simp at erasedLength
                  omega
              | cons d tail =>
                  let contextWord :=
                    (((Word.singleton a ++ Word.singleton b) ++
                      Word.singleton c) ++ wordOfCons d tail)
                  let arranged := contextWord ++ Word.singleton marker
                  have wordPerm : word.toList.Perm arranged.toList := by
                    have erasePerm := List.perm_cons_erase present
                    rw [erased] at erasePerm
                    have rotatePerm :
                        (marker :: a :: b :: c :: d :: tail).Perm
                          ((a :: b :: c :: d :: tail) ++ [marker]) := by
                      simpa using
                        perm_append_comm [marker] (a :: b :: c :: d :: tail)
                    simpa [arranged, contextWord, wordOfCons, Word.singleton,
                      Word.toList_append, List.append_assoc] using
                        erasePerm.trans rotatePerm
                  have enter := derivesPermutation word arranged wordPerm
                  have duplicate :=
                    derivesDuplicateFifth
                      (Word.singleton a) (Word.singleton b)
                      (Word.singleton c) (wordOfCons d tail)
                      (Word.singleton marker)
                  have exit :
                      Derives rootBasis
                        (arranged ++ Word.singleton marker)
                        (word ++ Word.singleton marker) :=
                    derivesPermutation _ _ <| by
                      rw [List.perm_iff_count]
                      intro z
                      have counts := List.perm_iff_count.mp wordPerm z
                      simp only [Word.toList_append, List.count_append]
                      omega
                  have duplicated :
                      Derives rootBasis arranged
                        (arranged ++ Word.singleton marker) := by
                    simpa only [arranged, contextWord] using
                      duplicate
                  exact Derives.trans enter (Derives.trans duplicated exit)

/-- Insert four copies of a supported marker into any word of length at
least five. -/
theorem derivesInsertFourSupported
    (word : Word Nat) (marker : Nat)
    (long : 5 ≤ word.toList.length)
    (present : marker ∈ word.toList) :
    Derives rootBasis word
      (((Word.singleton marker ++ Word.singleton marker) ++
          Word.singleton marker) ++ Word.singleton marker ++ word) := by
  let m := Word.singleton marker
  have first := derivesAppendMember word marker long present
  have second := derivesAppendMember (word ++ m) marker (by
    simp only [Word.toList_append, List.length_append]
    have mPositive : 0 < m.toList.length := by simp [m, Word.toList]
    omega) (by
      simp [m, Word.toList_append])
  have third := derivesAppendMember ((word ++ m) ++ m) marker (by
    simp only [Word.toList_append, List.length_append]
    have mPositive : 0 < m.toList.length := by simp [m, Word.toList]
    omega) (by simp [m, Word.toList_append])
  have fourth := derivesAppendMember (((word ++ m) ++ m) ++ m) marker (by
    simp only [Word.toList_append, List.length_append]
    have mPositive : 0 < m.toList.length := by simp [m, Word.toList]
    omega) (by simp [m, Word.toList_append])
  exact first.trans <| second.trans <| third.trans <| fourth.trans <|
    derivesPermutation _ _ <| by
      have rotate :
          (word.toList ++ [marker, marker, marker, marker]).Perm
            ([marker, marker, marker, marker] ++ word.toList) :=
        perm_append_comm word.toList [marker, marker, marker, marker]
      simpa [m, Word.toList_append, Word.singleton, Word.toList,
        List.append_assoc] using rotate

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

theorem derivesContextIdempotence
    (a b c d u : Word Nat) :
    Derives rootBasis
      ((((a ++ b) ++ c) ++ d) ++ (u ++ u))
      ((((a ++ b) ++ c) ++ d) ++ u) := by
  simpa [Word.append_assoc] using
    Derives.symm (derivesDuplicateFifth a b c d u)

/-- Replay commutative-idempotent derivations behind four fixed nonempty
markers, where the root's degree-five duplication law supplies idempotence. -/
theorem liftSemilattice
    {u v : Word Nat}
    (derivation : Derives semilatticeBasis u v)
    (a b c d : Word Nat) (σ : Nat → Word Nat) :
    Derives rootBasis
      ((((a ++ b) ++ c) ++ d) ++ u.bind σ)
      ((((a ++ b) ++ c) ++ d) ++ v.bind σ) := by
  induction derivation generalizing a b c d σ with
  | fromBasis member =>
      simp only [semilatticeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [semilatticeIdempotenceLaw, semilatticeXX,
          semilatticeX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            derivesContextIdempotence a b c d (σ 0)
      · have commute := derivesCommutativity (σ 0) (σ 1)
        simpa [semilatticeCommutativityLaw, semilatticeXY,
          semilatticeYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
            Derives.prepend (((a ++ b) ++ c) ++ d) commute
  | refl =>
      exact Derives.refl _
  | symm nestedDerivation inductionHypothesis =>
      exact Derives.symm (inductionHypothesis a b c d σ)
  | trans firstDerivation secondDerivation firstHypothesis secondHypothesis =>
      exact Derives.trans
        (firstHypothesis a b c d σ)
        (secondHypothesis a b c d σ)
  | prepend stem nestedDerivation inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        inductionHypothesis a b c (d ++ stem.bind σ) σ
  | appendRight nestedDerivation suffix inductionHypothesis =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight
          (inductionHypothesis a b c d σ) (suffix.bind σ)
  | subst nestedDerivation firstSubstitution inductionHypothesis =>
      simpa [bind_bind] using
        inductionHypothesis a b c d
          (fun x => (firstSubstitution x).bind σ)

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

private theorem count_three_eq_length
    (a b c : Nat) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ∀ xs : List Nat,
      (∀ z, z ∈ xs → z = a ∨ z = b ∨ z = c) →
      xs.count a + xs.count b + xs.count c = xs.length
  | [], _ => by simp
  | x :: xs, members => by
      have head := members x (by simp)
      have tailMembers :
          ∀ z, z ∈ xs → z = a ∨ z = b ∨ z = c := by
        intro z member
        exact members z (by simp [member])
      have ih :=
        count_three_eq_length a b c ab ac bc xs tailMembers
      rcases head with rfl | rfl | rfl
      · rw [List.count_cons_self,
          List.count_cons_of_ne ab,
          List.count_cons_of_ne ac,
          List.length_cons]
        omega
      · rw [List.count_cons_of_ne (Ne.symm ab),
          List.count_cons_self,
          List.count_cons_of_ne bc,
          List.length_cons]
        omega
      · rw [List.count_cons_of_ne (Ne.symm ac),
          List.count_cons_of_ne (Ne.symm bc),
          List.count_cons_self,
          List.length_cons]
        omega

private theorem count_four_eq_length
    (a b c d : Nat)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
    (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) :
    ∀ xs : List Nat,
      (∀ z, z ∈ xs → z = a ∨ z = b ∨ z = c ∨ z = d) →
      xs.count a + xs.count b + xs.count c + xs.count d =
        xs.length
  | [], _ => by simp
  | x :: xs, members => by
      have head := members x (by simp)
      have tailMembers :
          ∀ z, z ∈ xs →
            z = a ∨ z = b ∨ z = c ∨ z = d := by
        intro z member
        exact members z (by simp [member])
      have ih :=
        count_four_eq_length a b c d ab ac ad bc bd cd xs
          tailMembers
      rcases head with rfl | rfl | rfl | rfl
      · rw [List.count_cons_self,
          List.count_cons_of_ne ab,
          List.count_cons_of_ne ac,
          List.count_cons_of_ne ad,
          List.length_cons]
        omega
      · rw [List.count_cons_of_ne (Ne.symm ab),
          List.count_cons_self,
          List.count_cons_of_ne bc,
          List.count_cons_of_ne bd,
          List.length_cons]
        omega
      · rw [List.count_cons_of_ne (Ne.symm ac),
          List.count_cons_of_ne (Ne.symm bc),
          List.count_cons_self,
          List.count_cons_of_ne cd,
          List.length_cons]
        omega
      · rw [List.count_cons_of_ne (Ne.symm ad),
          List.count_cons_of_ne (Ne.symm bd),
          List.count_cons_of_ne (Ne.symm cd),
          List.count_cons_self,
          List.length_cons]
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

private theorem triple_perm_of_counts
    {a b c : Nat} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    {xs ys : List Nat}
    (xsMembers : ∀ z, z ∈ xs → z = a ∨ z = b ∨ z = c)
    (ysMembers : ∀ z, z ∈ ys → z = a ∨ z = b ∨ z = c)
    (countA : xs.count a = ys.count a)
    (countB : xs.count b = ys.count b)
    (countC : xs.count c = ys.count c) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro z
  by_cases za : z = a
  · subst z
    exact countA
  · by_cases zb : z = b
    · subst z
      exact countB
    · by_cases zc : z = c
      · subst z
        exact countC
      · have xsZero : xs.count z = 0 :=
          List.count_eq_zero.mpr <| by
            intro member
            rcases xsMembers z member with equal | equal | equal
            · exact za equal
            · exact zb equal
            · exact zc equal
        have ysZero : ys.count z = 0 :=
          List.count_eq_zero.mpr <| by
            intro member
            rcases ysMembers z member with equal | equal | equal
            · exact za equal
            · exact zb equal
            · exact zc equal
        rw [xsZero, ysZero]

private theorem four_perm_of_counts
    {a b c d : Nat}
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
    (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d)
    {xs ys : List Nat}
    (xsMembers :
      ∀ z, z ∈ xs → z = a ∨ z = b ∨ z = c ∨ z = d)
    (ysMembers :
      ∀ z, z ∈ ys → z = a ∨ z = b ∨ z = c ∨ z = d)
    (countA : xs.count a = ys.count a)
    (countB : xs.count b = ys.count b)
    (countC : xs.count c = ys.count c)
    (countD : xs.count d = ys.count d) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro z
  by_cases za : z = a
  · subst z
    exact countA
  · by_cases zb : z = b
    · subst z
      exact countB
    · by_cases zc : z = c
      · subst z
        exact countC
      · by_cases zd : z = d
        · subst z
          exact countD
        · have xsZero : xs.count z = 0 :=
            List.count_eq_zero.mpr <| by
              intro member
              rcases xsMembers z member with
                equal | equal | equal | equal
              · exact za equal
              · exact zb equal
              · exact zc equal
              · exact zd equal
          have ysZero : ys.count z = 0 :=
            List.count_eq_zero.mpr <| by
              intro member
              rcases ysMembers z member with
                equal | equal | equal | equal
              · exact za equal
              · exact zb equal
              · exact zc equal
              · exact zd equal
          rw [xsZero, ysZero]

private theorem pairQuadrupleToCanonical
    (a b p q r s : Nat) (ab : a ≠ b)
    (support :
      ∀ z, z ∈ [p, q, r, s] ↔ z = a ∨ z = b) :
    Derives rootBasis
      (wordOfCons p [q, r, s])
      (wordOfCons a [a, a, b]) := by
  let source := [p, q, r, s]
  have sourceMembers :
      ∀ z, z ∈ source → z = a ∨ z = b := by
    intro z member
    exact (support z).mp member
  have aPositive : 0 < source.count a :=
    List.count_pos_iff.mpr <| (support a).mpr (Or.inl rfl)
  have bPositive : 0 < source.count b :=
    List.count_pos_iff.mpr <| (support b).mpr (Or.inr rfl)
  have countSum :=
    count_pair_eq_length a b ab source sourceMembers
  have sourceLength : source.length = 4 := by
    simp [source]
  have countCases :
      source.count a = 1 ∨ source.count a = 2 ∨
        source.count a = 3 := by
    omega
  rcases countCases with countA | countA | countA
  · have countB : source.count b = 3 := by omega
    have arrange :
        source.Perm [a, b, b, b] :=
      pair_perm_of_counts ab sourceMembers
        (by
          intro z member
          simpa [or_assoc, or_left_comm, or_comm] using member)
        (by simpa [source, ab, Ne.symm ab] using countA)
        (by simpa [source, ab, Ne.symm ab] using countB)
    have first :
        Derives rootBasis
          (wordOfCons p [q, r, s])
          (wordOfCons a [b, b, b]) :=
      derivesPermutation _ _ <| by
        simpa [source, wordOfCons, Word.toList] using arrange
    have transferOne :
        Derives rootBasis
          (wordOfCons a [b, b, b])
          (wordOfCons a [a, b, b]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton b)
            (Word.singleton b)
    have arrangeTwo :
        Derives rootBasis
          (wordOfCons a [a, b, b])
          (wordOfCons a [b, b, a]) :=
      derivesPermutation _ _ (by
        rw [List.perm_iff_count]
        intro z
        simp only [wordOfCons, Word.toList, List.count_cons,
          List.count_nil]
        omega)
    have transferTwo :
        Derives rootBasis
          (wordOfCons a [b, b, a])
          (wordOfCons a [a, b, a]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton b)
            (Word.singleton a)
    have finish :
        Derives rootBasis
          (wordOfCons a [a, b, a])
          (wordOfCons a [a, a, b]) :=
      derivesPermutation _ _ (by
        rw [List.perm_iff_count]
        intro z
        simp only [wordOfCons, Word.toList, List.count_cons,
          List.count_nil]
        omega)
    exact first.trans <|
      transferOne.trans <|
      arrangeTwo.trans <|
      transferTwo.trans finish
  · have countB : source.count b = 2 := by omega
    have arrange :
        source.Perm [a, b, b, a] :=
      pair_perm_of_counts ab sourceMembers
        (by
          intro z member
          simpa [or_assoc, or_left_comm, or_comm] using member)
        (by simpa [source, ab, Ne.symm ab] using countA)
        (by simpa [source, ab, Ne.symm ab] using countB)
    have first :
        Derives rootBasis
          (wordOfCons p [q, r, s])
          (wordOfCons a [b, b, a]) :=
      derivesPermutation _ _ <| by
        simpa [source, wordOfCons, Word.toList] using arrange
    have transfer :
        Derives rootBasis
          (wordOfCons a [b, b, a])
          (wordOfCons a [a, b, a]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton b)
            (Word.singleton a)
    have finish :
        Derives rootBasis
          (wordOfCons a [a, b, a])
          (wordOfCons a [a, a, b]) :=
      derivesPermutation _ _ (by
        rw [List.perm_iff_count]
        intro z
        simp only [wordOfCons, Word.toList, List.count_cons,
          List.count_nil]
        omega)
    exact first.trans (transfer.trans finish)
  · have countB : source.count b = 1 := by omega
    have arrange :
        source.Perm [a, a, a, b] :=
      pair_perm_of_counts ab sourceMembers
        (by
          intro z member
          simpa [or_assoc, or_left_comm, or_comm] using member)
        (by simpa [source, ab, Ne.symm ab] using countA)
        (by simpa [source, ab, Ne.symm ab] using countB)
    exact derivesPermutation _ _ <| by
      simpa [source, wordOfCons, Word.toList] using arrange

private theorem tripleQuadrupleToCanonical
    (a b c p q r s : Nat)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (support :
      ∀ z, z ∈ [p, q, r, s] ↔ z = a ∨ z = b ∨ z = c) :
    Derives rootBasis
      (wordOfCons p [q, r, s])
      (wordOfCons a [a, b, c]) := by
  let source := [p, q, r, s]
  have sourceMembers :
      ∀ z, z ∈ source → z = a ∨ z = b ∨ z = c := by
    intro z member
    exact (support z).mp member
  have aPositive : 0 < source.count a :=
    List.count_pos_iff.mpr <|
      (support a).mpr (Or.inl rfl)
  have bPositive : 0 < source.count b :=
    List.count_pos_iff.mpr <|
      (support b).mpr (Or.inr (Or.inl rfl))
  have cPositive : 0 < source.count c :=
    List.count_pos_iff.mpr <|
      (support c).mpr (Or.inr (Or.inr rfl))
  have countSum :=
    count_three_eq_length a b c ab ac bc source sourceMembers
  have sourceLength : source.length = 4 := by
    simp [source]
  have doubled :
      source.count a = 2 ∨ source.count b = 2 ∨
        source.count c = 2 := by
    omega
  rcases doubled with doubledA | doubledB | doubledC
  · have countB : source.count b = 1 := by omega
    have countC : source.count c = 1 := by omega
    have arrange :
        source.Perm [a, a, b, c] :=
      triple_perm_of_counts ab ac bc sourceMembers
        (by
          intro z member
          simpa [or_assoc, or_left_comm, or_comm] using member)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using doubledA)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using countB)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using countC)
    exact derivesPermutation _ _ <| by
      simpa [source, wordOfCons, Word.toList] using arrange
  · have countA : source.count a = 1 := by omega
    have countC : source.count c = 1 := by omega
    have arrange :
        source.Perm [a, b, b, c] :=
      triple_perm_of_counts ab ac bc sourceMembers
        (by
          intro z member
          simpa [or_assoc, or_left_comm, or_comm] using member)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using countA)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using doubledB)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using countC)
    have first :
        Derives rootBasis
          (wordOfCons p [q, r, s])
          (wordOfCons a [b, b, c]) :=
      derivesPermutation _ _ <| by
        simpa [source, wordOfCons, Word.toList] using arrange
    have transfer :
        Derives rootBasis
          (wordOfCons a [b, b, c])
          (wordOfCons a [a, b, c]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton b)
            (Word.singleton c)
    exact first.trans transfer
  · have countA : source.count a = 1 := by omega
    have countB : source.count b = 1 := by omega
    have arrange :
        source.Perm [a, c, c, b] :=
      triple_perm_of_counts ab ac bc sourceMembers
        (by
          intro z member
          simpa [or_assoc, or_left_comm, or_comm] using member)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using countA)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using countB)
        (by simpa [source, ab, ac, bc, Ne.symm ab, Ne.symm ac,
          Ne.symm bc] using doubledC)
    have first :
        Derives rootBasis
          (wordOfCons p [q, r, s])
          (wordOfCons a [c, c, b]) :=
      derivesPermutation _ _ <| by
        simpa [source, wordOfCons, Word.toList] using arrange
    have transfer :
        Derives rootBasis
          (wordOfCons a [c, c, b])
          (wordOfCons a [a, c, b]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton c)
            (Word.singleton b)
    have finish :
        Derives rootBasis
          (wordOfCons a [a, c, b])
          (wordOfCons a [a, b, c]) :=
      derivesPermutation _ _ (by
        rw [List.perm_iff_count]
        intro z
        simp only [wordOfCons, Word.toList, List.count_cons,
          List.count_nil]
        omega)
    exact first.trans (transfer.trans finish)

private theorem fourQuadrupleToCanonical
    (a b c d p q r s : Nat)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
    (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d)
    (support :
      ∀ z,
        z ∈ [p, q, r, s] ↔
          z = a ∨ z = b ∨ z = c ∨ z = d) :
    Derives rootBasis
      (wordOfCons p [q, r, s])
      (wordOfCons a [b, c, d]) := by
  let source := [p, q, r, s]
  have sourceMembers :
      ∀ z, z ∈ source →
        z = a ∨ z = b ∨ z = c ∨ z = d := by
    intro z member
    exact (support z).mp member
  have aPositive : 0 < source.count a :=
    List.count_pos_iff.mpr <|
      (support a).mpr (Or.inl rfl)
  have bPositive : 0 < source.count b :=
    List.count_pos_iff.mpr <|
      (support b).mpr (Or.inr (Or.inl rfl))
  have cPositive : 0 < source.count c :=
    List.count_pos_iff.mpr <|
      (support c).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have dPositive : 0 < source.count d :=
    List.count_pos_iff.mpr <|
      (support d).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have countSum :=
    count_four_eq_length a b c d ab ac ad bc bd cd source
      sourceMembers
  have sourceLength : source.length = 4 := by
    simp [source]
  have countA : source.count a = 1 := by omega
  have countB : source.count b = 1 := by omega
  have countC : source.count c = 1 := by omega
  have countD : source.count d = 1 := by omega
  have arrange :
      source.Perm [a, b, c, d] :=
    four_perm_of_counts ab ac ad bc bd cd sourceMembers
      (by
        intro z member
        simpa [or_assoc, or_left_comm, or_comm] using member)
      (by simpa [source, ab, ac, ad, bc, bd, cd, Ne.symm ab,
        Ne.symm ac, Ne.symm ad, Ne.symm bc, Ne.symm bd,
        Ne.symm cd] using countA)
      (by simpa [source, ab, ac, ad, bc, bd, cd, Ne.symm ab,
        Ne.symm ac, Ne.symm ad, Ne.symm bc, Ne.symm bd,
        Ne.symm cd] using countB)
      (by simpa [source, ab, ac, ad, bc, bd, cd, Ne.symm ab,
        Ne.symm ac, Ne.symm ad, Ne.symm bc, Ne.symm bd,
        Ne.symm cd] using countC)
      (by simpa [source, ab, ac, ad, bc, bd, cd, Ne.symm ab,
        Ne.symm ac, Ne.symm ad, Ne.symm bc, Ne.symm bd,
        Ne.symm cd] using countD)
  exact derivesPermutation _ _ <| by
    simpa [source, wordOfCons, Word.toList] using arrange

private theorem pairQuadruplesDerive
    (a b p q r s u v w t : Nat) (ab : a ≠ b)
    (leftSupport :
      ∀ z, z ∈ [p, q, r, s] ↔ z = a ∨ z = b)
    (rightSupport :
      ∀ z, z ∈ [u, v, w, t] ↔ z = a ∨ z = b) :
    Derives rootBasis
      (wordOfCons p [q, r, s])
      (wordOfCons u [v, w, t]) :=
  (pairQuadrupleToCanonical a b p q r s ab leftSupport).trans <|
    (pairQuadrupleToCanonical a b u v w t ab rightSupport).symm

private theorem tripleQuadruplesDerive
    (a b c p q r s u v w t : Nat)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (leftSupport :
      ∀ z, z ∈ [p, q, r, s] ↔ z = a ∨ z = b ∨ z = c)
    (rightSupport :
      ∀ z, z ∈ [u, v, w, t] ↔ z = a ∨ z = b ∨ z = c) :
    Derives rootBasis
      (wordOfCons p [q, r, s])
      (wordOfCons u [v, w, t]) :=
  (tripleQuadrupleToCanonical
    a b c p q r s ab ac bc leftSupport).trans <|
      (tripleQuadrupleToCanonical
        a b c u v w t ab ac bc rightSupport).symm

private theorem derivesQuadrupleSupport
    (a b c d p q r s : Nat)
    (support :
      ∀ z, z ∈ [a, b, c, d] ↔ z ∈ [p, q, r, s]) :
    Derives rootBasis
      (wordOfCons a [b, c, d])
      (wordOfCons p [q, r, s]) := by
  by_cases ab : a = b
  · subst b
    by_cases ac : a = c
    · subst c
      by_cases ad : a = d
      · subst d
        have hp : p = a := by
          simpa using (support p).mpr (by simp)
        have hq : q = a := by
          simpa using (support q).mpr (by simp)
        have hr : r = a := by
          simpa using (support r).mpr (by simp)
        have hs : s = a := by
          simpa using (support s).mpr (by simp)
        subst p
        subst q
        subst r
        subst s
        exact Derives.refl _
      · apply pairQuadruplesDerive a d
          a a a d p q r s ad
        · intro z
          simp [or_assoc, or_left_comm, or_comm]
        · intro z
          exact (support z).symm.trans
            (by simp [or_assoc, or_left_comm, or_comm])
    · by_cases ad : a = d
      · subst d
        apply pairQuadruplesDerive a c
            a a c a p q r s ac
        · intro z
          simp [or_assoc, or_left_comm, or_comm]
        · intro z
          exact (support z).symm.trans
            (by simp [or_assoc, or_left_comm, or_comm])
      · by_cases cd : c = d
        · subst d
          apply pairQuadruplesDerive a c
              a a c c p q r s ac
          · intro z
            simp [or_assoc, or_left_comm, or_comm]
          · intro z
            exact (support z).symm.trans
              (by simp [or_assoc, or_left_comm, or_comm])
        · apply tripleQuadruplesDerive a c d
            a a c d p q r s ac ad cd
          · intro z
            simp [or_assoc, or_left_comm, or_comm]
          · intro z
            exact (support z).symm.trans
              (by simp [or_assoc, or_left_comm, or_comm])
  · by_cases ac : a = c
    · subst c
      by_cases ad : a = d
      · subst d
        apply pairQuadruplesDerive a b
            a b a a p q r s ab
        · intro z
          simp [or_assoc, or_left_comm, or_comm]
        · intro z
          exact (support z).symm.trans
            (by simp [or_assoc, or_left_comm, or_comm])
      · by_cases bd : b = d
        · subst d
          apply pairQuadruplesDerive a b
              a b a b p q r s ab
          · intro z
            simp [or_assoc, or_left_comm, or_comm]
          · intro z
            exact (support z).symm.trans
              (by simp [or_assoc, or_left_comm, or_comm])
        · apply tripleQuadruplesDerive a b d
            a b a d p q r s ab ad bd
          · intro z
            simp [or_assoc, or_left_comm, or_comm]
          · intro z
            exact (support z).symm.trans
              (by simp [or_assoc, or_left_comm, or_comm])
    · by_cases bc : b = c
      · subst c
        by_cases ad : a = d
        · subst d
          apply pairQuadruplesDerive a b
              a b b a p q r s ab
          · intro z
            simp [or_assoc, or_left_comm, or_comm]
          · intro z
            exact (support z).symm.trans
              (by simp [or_assoc, or_left_comm, or_comm])
        · by_cases bd : b = d
          · subst d
            apply pairQuadruplesDerive a b
                a b b b p q r s ab
            · intro z
              simp [or_assoc, or_left_comm, or_comm]
            · intro z
              exact (support z).symm.trans
                (by simp [or_assoc, or_left_comm, or_comm])
          · apply tripleQuadruplesDerive a b d
              a b b d p q r s ab ad bd
            · intro z
              simp [or_assoc, or_left_comm, or_comm]
            · intro z
              exact (support z).symm.trans
                (by simp [or_assoc, or_left_comm, or_comm])
      · by_cases ad : a = d
        · subst d
          apply tripleQuadruplesDerive a b c
              a b c a p q r s ab ac bc
          · intro z
            simp [or_assoc, or_left_comm, or_comm]
          · intro z
            exact (support z).symm.trans
              (by simp [or_assoc, or_left_comm, or_comm])
        · by_cases bd : b = d
          · subst d
            apply tripleQuadruplesDerive a b c
                a b c b p q r s ab ac bc
            · intro z
              simp [or_assoc, or_left_comm, or_comm]
            · intro z
              exact (support z).symm.trans
                (by simp [or_assoc, or_left_comm, or_comm])
          · by_cases cd : c = d
            · subst d
              apply tripleQuadruplesDerive a b c
                  a b c c p q r s ab ac bc
              · intro z
                simp [or_assoc, or_left_comm, or_comm]
              · intro z
                exact (support z).symm.trans
                  (by simp [or_assoc, or_left_comm, or_comm])
            · have rightSupport :
                  ∀ z,
                    z ∈ [p, q, r, s] ↔
                      z = a ∨ z = b ∨ z = c ∨ z = d := by
                intro z
                exact (support z).symm.trans
                  (by simp [or_assoc, or_left_comm, or_comm])
              exact Derives.symm <|
                fourQuadrupleToCanonical
                  a b c d p q r s ab ac ad bc bd cd rightSupport

private theorem word_eq_of_length_four
    (w : Word Nat) (lengthFour : w.toList.length = 4) :
    ∃ a b c d, w = wordOfCons a [b, c, d] := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at lengthFour
      | cons second rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at lengthFour
          | cons third more =>
              cases more with
              | nil =>
                  simp [Word.toList] at lengthFour
              | cons fourth remaining =>
                  have remainingNil : remaining = [] := by
                    simp [Word.toList] at lengthFour
                    omega
                  subst remaining
                  exact ⟨head, second, third, fourth, rfl⟩

/-- Words of length four are classified exactly by variable support. -/
theorem derivesLengthFourSupport
    (u v : Word Nat)
    (uFour : u.toList.length = 4)
    (vFour : v.toList.length = 4)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
    Derives rootBasis u v := by
  obtain ⟨a, b, c, d, leftShape⟩ :=
    word_eq_of_length_four u uFour
  obtain ⟨p, q, r, s, rightShape⟩ :=
    word_eq_of_length_four v vFour
  rw [leftShape, rightShape] at support ⊢
  exact derivesQuadrupleSupport a b c d p q r s <| by
    intro z
    simpa [wordOfCons, Word.toList] using support z

/-- Long words valid in the semilattice factor are equal after four copies
of a common supported marker are inserted. -/
theorem derivesLongOfSemilatticeValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S2_3.table.semigroup)
    (leftLong : 5 ≤ identity.lhs.toList.length)
    (rightLong : 5 ≤ identity.rhs.toList.length) :
    Derives rootBasis identity.lhs identity.rhs := by
  have semilatticeValid :
      identity.SatisfiedBy semilatticeTwo.semigroup := by
    rw [← SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family.catalogueS2_3_table_eq_semilatticeTwo]
    exact leftValid
  have support := semilatticeValid_support_eq identity semilatticeValid
  let marker := identity.lhs.head
  let markerWord := Word.singleton marker
  have markerInLeft : marker ∈ identity.lhs.toList := by
    simp [marker, Word.toList]
  have markerInRight : marker ∈ identity.rhs.toList :=
    (support marker).mp markerInLeft
  have insertLeft :=
    derivesInsertFourSupported identity.lhs marker leftLong markerInLeft
  have insertRight :=
    derivesInsertFourSupported identity.rhs marker rightLong markerInRight
  have semilatticeDerivation :=
    semilatticeBasis_complete.2 identity semilatticeValid
  have lifted :=
    liftSemilattice semilatticeDerivation
      markerWord markerWord markerWord markerWord Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact insertLeft.trans <| lifted.trans (Derives.symm insertRight)

/-- Factor validity is sufficient for a root derivation in every S5_194
length stratum. -/
theorem derivesOfFactorValidity
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S2_3.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_194.table.semigroup) :
    Derives rootBasis identity.lhs identity.rhs := by
  have semilatticeValid :
      identity.SatisfiedBy semilatticeTwo.semigroup := by
    rw [← SemigroupBasis.CoRoots.Order6GenericCASSubdirectS5_194Family.catalogueS2_3_table_eq_semilatticeTwo]
    exact leftValid
  have support := semilatticeValid_support_eq identity semilatticeValid
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
  | four leftFour rightFour _ =>
      exact derivesLengthFourSupport identity.lhs identity.rhs
        leftFour rightFour support
  | long leftLong rightLong =>
      exact derivesLongOfSemilatticeValid identity leftValid
        leftLong rightLong

end Family

abbrev rootSemigroup :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.oppositeTable.semigroup

abbrev rootBasis :=
  SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.basis

abbrev leftFactor :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5368.leftFactor

abbrev rightFactor :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5368.rightFactor

private abbrev factorPair :=
  SemigroupBasis.Generated.Order6GenericCASSubdirectWitnesses.S6_5368.subdirectPair

private theorem leftFactorModels : Models leftFactor rootBasis := by
  intro identity member
  exact factorPair.left.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.models
      identity member)

private theorem rightFactorModels : Models rightFactor rootBasis := by
  intro identity member
  exact factorPair.right.pushforwardIdentity identity
    (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5368.models
      identity member)

/-- Exact unconditional basis endpoint for the mixed generic-CAS root
`S6_5368`. -/
theorem basisFor : BasisFor rootSemigroup rootBasis :=
  (IntersectionBasis.mk leftFactorModels rightFactorModels
    Family.derivesOfFactorValidity).basisFor factorPair

end SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_5368

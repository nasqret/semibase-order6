import SemigroupBasis.Equational

namespace SemigroupBasis.CoRoots.S5_194

open SemigroupBasis

def xy : Word Nat := ⟨0, [1]⟩
def yx : Word Nat := ⟨1, [0]⟩
def xyztuv : Word Nat := ⟨0, [1, 2, 3, 4, 5]⟩
def yztuv : Word Nat := ⟨1, [2, 3, 4, 5]⟩
def xyyt : Word Nat := ⟨0, [1, 1, 2]⟩
def xxyt : Word Nat := ⟨0, [0, 1, 2]⟩

def commutativityLaw : Identity Nat := ⟨xy, yx⟩
def longCancellationLaw : Identity Nat := ⟨xyztuv, yztuv⟩
def multiplicityTransferLaw : Identity Nat := ⟨xyyt, xxyt⟩

/-- The exact recorded basis for the cyclic semigroup `C_{5,1}`. -/
def basis : List (Identity Nat) :=
  [commutativityLaw, longCancellationLaw, multiplicityTransferLaw]

private def instantiateSixWords
    (u v w t r s : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => t
  | 4 => r
  | 5 => s
  | n + 6 => Word.singleton (n + 6)

theorem derivesCommutativity (u v : Word Nat) :
    Derives basis (u ++ v) (v ++ u) := by
  have base : Derives basis xy yx :=
    Derives.fromBasis (e := commutativityLaw) <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateSixWords u v v v v v)
  simpa [basis, commutativityLaw, xy, yx, instantiateSixWords,
    Word.bind, Word.append, Word.singleton] using substituted

theorem derivesDropPrefix
    (u v w t r s : Word Nat) :
    Derives basis
      (((((u ++ v) ++ w) ++ t) ++ r) ++ s)
      ((((v ++ w) ++ t) ++ r) ++ s) := by
  have base : Derives basis xyztuv yztuv :=
    Derives.fromBasis (e := longCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have substituted :=
    Derives.subst base (instantiateSixWords u v w t r s)
  simpa [basis, longCancellationLaw, xyztuv, yztuv,
    instantiateSixWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

theorem derivesMultiplicityTransfer
    (u v t : Word Nat) :
    Derives basis
      (((u ++ v) ++ v) ++ t)
      (((u ++ u) ++ v) ++ t) := by
  have base : Derives basis xyyt xxyt :=
    Derives.fromBasis (e := multiplicityTransferLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have substituted :=
    Derives.subst base (instantiateSixWords u v t t t t)
  simpa [basis, multiplicityTransferLaw, xyyt, xxyt,
    instantiateSixWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using substituted

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem listDerives_of_perm {xs ys : List Nat}
    (permutation : xs.Perm ys) : ListDerives xs ys := by
  induction permutation with
  | nil =>
      exact ListDerives.empty
  | cons x _ ih =>
      cases ih with
      | empty =>
          exact ListDerives.words (Derives.refl _)
      | words derivation =>
          exact ListDerives.words <| by
            simpa [wordOfCons, Word.singleton, Word.append] using
              Derives.prepend (Word.singleton x) derivation
  | swap x y xs =>
      exact ListDerives.words <| by
        cases xs with
        | nil =>
            simpa [wordOfCons, Word.append, Word.singleton] using
              derivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (derivesCommutativity
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ first second =>
      cases first with
      | empty =>
          cases second
          exact ListDerives.empty
      | words firstDerivation =>
          cases second with
          | words secondDerivation =>
              exact ListDerives.words
                (Derives.trans firstDerivation secondDerivation)

theorem derivesPermutation (u v : Word Nat)
    (permutation : u.toList.Perm v.toList) :
    Derives basis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm permutation with
          | words derivation =>
              exact derivation

private def longMarker : Word Nat :=
  wordOfCons 0 [0, 0, 0, 0]

private theorem derivesReplaceFirst
    (a b c d e marker : Nat) :
    Derives basis
      (wordOfCons a [b, c, d, e])
      (wordOfCons marker [b, c, d, e]) := by
  have insert :=
    Derives.symm <|
      derivesDropPrefix
        (Word.singleton marker) (Word.singleton a)
        (Word.singleton b) (Word.singleton c)
        (Word.singleton d) (Word.singleton e)
  have commute :=
    Derives.appendRight
      (derivesCommutativity
        (Word.singleton marker) (Word.singleton a))
      (((Word.singleton b ++ Word.singleton c) ++
        Word.singleton d) ++ Word.singleton e)
  have remove :=
    derivesDropPrefix
      (Word.singleton a) (Word.singleton marker)
      (Word.singleton b) (Word.singleton c)
      (Word.singleton d) (Word.singleton e)
  exact Derives.trans
    (by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using insert)
    (Derives.trans
      (by
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using commute)
      (by
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using remove))

private theorem derivesFiveToMarker
    (a b c d e : Nat) :
    Derives basis (wordOfCons a [b, c, d, e]) longMarker := by
  have replaceA := derivesReplaceFirst a b c d e 0
  have arrangeB :
      Derives basis
        (wordOfCons 0 [b, c, d, e])
        (wordOfCons b [0, c, d, e]) :=
    derivesPermutation _ _ (by
      rw [List.perm_iff_count]
      intro z
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega)
  have replaceB := derivesReplaceFirst b 0 c d e 0
  have arrangeC :
      Derives basis
        (wordOfCons 0 [0, c, d, e])
        (wordOfCons c [0, 0, d, e]) :=
    derivesPermutation _ _ (by
      rw [List.perm_iff_count]
      intro z
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega)
  have replaceC := derivesReplaceFirst c 0 0 d e 0
  have arrangeD :
      Derives basis
        (wordOfCons 0 [0, 0, d, e])
        (wordOfCons d [0, 0, 0, e]) :=
    derivesPermutation _ _ (by
      rw [List.perm_iff_count]
      intro z
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega)
  have replaceD := derivesReplaceFirst d 0 0 0 e 0
  have arrangeE :
      Derives basis
        (wordOfCons 0 [0, 0, 0, e])
        (wordOfCons e [0, 0, 0, 0]) :=
    derivesPermutation _ _ (by
      rw [List.perm_iff_count]
      intro z
      simp only [wordOfCons, Word.toList, List.count_cons,
        List.count_nil]
      omega)
  have replaceE := derivesReplaceFirst e 0 0 0 0 0
  exact replaceA.trans <|
    arrangeB.trans <|
    replaceB.trans <|
    arrangeC.trans <|
    replaceC.trans <|
    arrangeD.trans <|
    replaceD.trans <|
    arrangeE.trans replaceE

private theorem derivesToMarker :
    ∀ (x : Nat) (xs : List Nat),
      5 ≤ (wordOfCons x xs).toList.length →
      Derives basis (wordOfCons x xs) longMarker
  | x, [], long => by
      simp [wordOfCons, Word.toList] at long
  | x, [y], long => by
      simp [wordOfCons, Word.toList] at long
  | x, [y, z], long => by
      simp [wordOfCons, Word.toList] at long
  | x, [y, z, t], long => by
      simp [wordOfCons, Word.toList] at long
  | x, [y, z, t, r], _ =>
      derivesFiveToMarker x y z t r
  | x, y :: z :: t :: r :: s :: ss, _ => by
      have drop :=
        derivesDropPrefix
          (Word.singleton x) (Word.singleton y)
          (Word.singleton z) (Word.singleton t)
          (Word.singleton r) (wordOfCons s ss)
      have rest :=
        derivesToMarker y (z :: t :: r :: s :: ss) (by
          simp [wordOfCons, Word.toList])
      exact Derives.trans
        (by
          simpa [wordOfCons, Word.singleton, Word.append,
            Word.append_assoc] using drop)
        rest
termination_by
  _ xs _ => xs.length

/-- All words of length at least five are derivably equal. -/
theorem derivesLongWords (u v : Word Nat)
    (uLong : 5 ≤ u.toList.length)
    (vLong : 5 ≤ v.toList.length) :
    Derives basis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          exact
            (derivesToMarker uHead uTail uLong).trans <|
              (derivesToMarker vHead vTail vLong).symm

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
    Derives basis
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
        Derives basis
          (wordOfCons p [q, r, s])
          (wordOfCons a [b, b, b]) :=
      derivesPermutation _ _ <| by
        simpa [source, wordOfCons, Word.toList] using arrange
    have transferOne :
        Derives basis
          (wordOfCons a [b, b, b])
          (wordOfCons a [a, b, b]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton b)
            (Word.singleton b)
    have arrangeTwo :
        Derives basis
          (wordOfCons a [a, b, b])
          (wordOfCons a [b, b, a]) :=
      derivesPermutation _ _ (by
        rw [List.perm_iff_count]
        intro z
        simp only [wordOfCons, Word.toList, List.count_cons,
          List.count_nil]
        omega)
    have transferTwo :
        Derives basis
          (wordOfCons a [b, b, a])
          (wordOfCons a [a, b, a]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton b)
            (Word.singleton a)
    have finish :
        Derives basis
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
        Derives basis
          (wordOfCons p [q, r, s])
          (wordOfCons a [b, b, a]) :=
      derivesPermutation _ _ <| by
        simpa [source, wordOfCons, Word.toList] using arrange
    have transfer :
        Derives basis
          (wordOfCons a [b, b, a])
          (wordOfCons a [a, b, a]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton b)
            (Word.singleton a)
    have finish :
        Derives basis
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
    Derives basis
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
        Derives basis
          (wordOfCons p [q, r, s])
          (wordOfCons a [b, b, c]) :=
      derivesPermutation _ _ <| by
        simpa [source, wordOfCons, Word.toList] using arrange
    have transfer :
        Derives basis
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
        Derives basis
          (wordOfCons p [q, r, s])
          (wordOfCons a [c, c, b]) :=
      derivesPermutation _ _ <| by
        simpa [source, wordOfCons, Word.toList] using arrange
    have transfer :
        Derives basis
          (wordOfCons a [c, c, b])
          (wordOfCons a [a, c, b]) := by
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesMultiplicityTransfer
            (Word.singleton a) (Word.singleton c)
            (Word.singleton b)
    have finish :
        Derives basis
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
    Derives basis
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
    Derives basis
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
    Derives basis
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
    Derives basis
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
    Derives basis u v := by
  obtain ⟨a, b, c, d, leftShape⟩ :=
    word_eq_of_length_four u uFour
  obtain ⟨p, q, r, s, rightShape⟩ :=
    word_eq_of_length_four v vFour
  rw [leftShape, rightShape] at support ⊢
  exact derivesQuadrupleSupport a b c d p q r s <| by
    intro z
    simpa [wordOfCons, Word.toList] using support z

end SemigroupBasis.CoRoots.S5_194

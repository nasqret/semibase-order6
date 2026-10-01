import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_199

open SemigroupBasis

def xxx : Word Nat := ⟨0, [0, 0]⟩
def xxxx : Word Nat := ⟨0, [0, 0, 0]⟩
def xxy : Word Nat := ⟨0, [0, 1]⟩
def xyx : Word Nat := ⟨0, [1, 0]⟩
def xyy : Word Nat := ⟨0, [1, 1]⟩
def yxx : Word Nat := ⟨1, [0, 0]⟩
def xxxy : Word Nat := ⟨0, [0, 0, 1]⟩
def xyz : Word Nat := ⟨0, [1, 2]⟩
def xzy : Word Nat := ⟨0, [2, 1]⟩
def yxz : Word Nat := ⟨1, [0, 2]⟩
def xxyz : Word Nat := ⟨0, [0, 1, 2]⟩

def powerLaw : Identity Nat := ⟨xxx, xxxx⟩
def firstSwapLaw : Identity Nat := ⟨xxy, xyx⟩
def transferLaw : Identity Nat := ⟨xxy, xyy⟩
def prefixSwapLaw : Identity Nat := ⟨xxy, yxx⟩
def heavyInsertionLaw : Identity Nat := ⟨xxy, xxxy⟩
def suffixCommutationLaw : Identity Nat := ⟨xyz, xzy⟩
def prefixCommutationLaw : Identity Nat := ⟨xyz, yxz⟩
def longInsertionLaw : Identity Nat := ⟨xyz, xxyz⟩

/-- The common published eight-identity basis of the `S5_199` family. -/
def basis : List (Identity Nat) :=
  [powerLaw, firstSwapLaw, transferLaw, prefixSwapLaw,
    heavyInsertionLaw, suffixCommutationLaw, prefixCommutationLaw,
    longInsertionLaw]

/-- The final three laws already generate the full published basis. -/
def coreBasis : List (Identity Nat) :=
  [suffixCommutationLaw, prefixCommutationLaw, longInsertionLaw]

def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

private theorem coreDerivesSuffixSwap (p u v : Word Nat) :
    Derives coreBasis ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase : Derives coreBasis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [coreBasis, suffixCommutationLaw, xyz, xzy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem coreDerivesPrefixSwap (u v q : Word Nat) :
    Derives coreBasis ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  have hbase : Derives coreBasis xyz yxz :=
    Derives.fromBasis (e := prefixCommutationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v q)
  simpa [coreBasis, prefixCommutationLaw, xyz, yxz,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem coreDerivesLongDuplication (u v w : Word Nat) :
    Derives coreBasis ((u ++ v) ++ w) (((u ++ u) ++ v) ++ w) := by
  have hbase : Derives coreBasis xyz xxyz :=
    Derives.fromBasis (e := longInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [coreBasis, longInsertionLaw, xyz, xxyz,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

private theorem coreDerivesPowerLaw :
    Derives coreBasis xxx xxxx := by
  simpa [xxx, xxxx, Word.singleton, Word.append,
    Word.append_assoc] using
      coreDerivesLongDuplication
        (Word.singleton 0) (Word.singleton 0) (Word.singleton 0)

private theorem coreDerivesFirstSwapLaw :
    Derives coreBasis xxy xyx := by
  simpa [xxy, xyx, Word.singleton, Word.append,
    Word.append_assoc] using
      coreDerivesSuffixSwap
        (Word.singleton 0) (Word.singleton 0) (Word.singleton 1)

private theorem coreDerivesPrefixSwapLaw :
    Derives coreBasis xxy yxx := by
  have first := coreDerivesFirstSwapLaw
  have second :=
    coreDerivesPrefixSwap
      (Word.singleton 0) (Word.singleton 1) (Word.singleton 0)
  exact Derives.trans first <| by
    simpa [xyx, yxx, Word.singleton, Word.append,
      Word.append_assoc] using second

private theorem coreDerivesHeavyInsertionLaw :
    Derives coreBasis xxy xxxy := by
  simpa [xxy, xxxy, Word.singleton, Word.append,
    Word.append_assoc] using
      coreDerivesLongDuplication
        (Word.singleton 0) (Word.singleton 0) (Word.singleton 1)

private theorem coreDerivesTransferLaw :
    Derives coreBasis xxy xyy := by
  have toYXX := coreDerivesPrefixSwapLaw
  have duplicateY :=
    coreDerivesLongDuplication
      (Word.singleton 1) (Word.singleton 0) (Word.singleton 0)
  have firstSwap :=
    coreDerivesSuffixSwap
      (Word.singleton 1) (Word.singleton 1) (Word.singleton 0)
  have firstSwapAppended :=
    Derives.appendRight firstSwap (Word.singleton 0)
  have secondSwap :=
    coreDerivesPrefixSwap
      (Word.singleton 1) (Word.singleton 0)
      (wordOfCons 1 [0])
  have thirdSwap :=
    coreDerivesSuffixSwap
      (Word.singleton 0) (wordOfCons 1 [1]) (Word.singleton 0)
  have contract :=
    Derives.symm <|
      coreDerivesLongDuplication
        (Word.singleton 0) (Word.singleton 1) (Word.singleton 1)
  exact Derives.trans toYXX <|
    Derives.trans
      (by
        simpa [yxx, Word.singleton, Word.append,
          Word.append_assoc] using duplicateY) <|
    Derives.trans
      (by
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using firstSwapAppended) <|
    Derives.trans
      (by
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using secondSwap) <|
    Derives.trans
      (by
        simpa [wordOfCons, Word.singleton, Word.append,
          Word.append_assoc] using thirdSwap) <| by
    simpa [xyy, wordOfCons, Word.singleton, Word.append,
      Word.append_assoc] using contract

private theorem publishedAxiomsDeriveFromCore
    (e : Identity Nat) (member : e ∈ basis) :
    Derives coreBasis e.lhs e.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact coreDerivesPowerLaw
  · exact coreDerivesFirstSwapLaw
  · exact coreDerivesTransferLaw
  · exact coreDerivesPrefixSwapLaw
  · exact coreDerivesHeavyInsertionLaw
  · exact Derives.fromBasis (e := suffixCommutationLaw) <| List.Mem.head _
  · exact Derives.fromBasis (e := prefixCommutationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  · exact Derives.fromBasis (e := longInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _

/-- Every derivation from the published basis can be replayed from the
three-law core. -/
theorem derivesCore {u v : Word Nat}
    (derivation : Derives basis u v) :
    Derives coreBasis u v :=
  derivation.transport publishedAxiomsDeriveFromCore

private theorem coreAxiomsDeriveFromPublished
    (e : Identity Nat) (member : e ∈ coreBasis) :
    Derives basis e.lhs e.rhs := by
  simp only [coreBasis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Derives.fromBasis (e := suffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  · exact Derives.fromBasis (e := prefixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  · exact Derives.fromBasis (e := longInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _

theorem derivesPublished {u v : Word Nat}
    (derivation : Derives coreBasis u v) :
    Derives basis u v :=
  derivation.transport coreAxiomsDeriveFromPublished

theorem derives_iff_core {u v : Word Nat} :
    Derives basis u v ↔ Derives coreBasis u v :=
  ⟨derivesCore, derivesPublished⟩

/-- Swap the final two nonempty blocks after a nonempty prefix. -/
theorem derivesSuffixSwap (p u v : Word Nat) :
    Derives basis ((p ++ u) ++ v) ((p ++ v) ++ u) := by
  have hbase : Derives basis xyz xzy :=
    Derives.fromBasis (e := suffixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords p u v)
  simpa [basis, suffixCommutationLaw, xyz, xzy,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Swap the first two nonempty blocks before a nonempty suffix. -/
theorem derivesPrefixSwap (u v q : Word Nat) :
    Derives basis ((u ++ v) ++ q) ((v ++ u) ++ q) := by
  have hbase : Derives basis xyz yxz :=
    Derives.fromBasis (e := prefixCommutationLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v q)
  simpa [basis, prefixCommutationLaw, xyz, yxz,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Duplicate the first nonempty block of a product of three nonempty blocks. -/
theorem derivesLongDuplication (u v w : Word Nat) :
    Derives basis ((u ++ v) ++ w) (((u ++ u) ++ v) ++ w) := by
  have hbase : Derives basis xyz xxyz :=
    Derives.fromBasis (e := longInsertionLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [basis, longInsertionLaw, xyz, xxyz,
    instantiateThreeWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

/-- Contract four consecutive copies of a nonempty block to three. -/
theorem derivesFourContraction (u : Word Nat) :
    Derives basis (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
  have hbase : Derives basis xxxx xxx :=
    Derives.symm <|
      Derives.fromBasis (e := powerLaw) <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u u u)
  simpa [basis, powerLaw, xxxx, xxx, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem ListDerives.trans {xs ys zs : List Nat}
    (first : ListDerives xs ys) (second : ListDerives ys zs) :
    ListDerives xs zs := by
  cases first with
  | empty =>
      cases second
      exact ListDerives.empty
  | words firstProof =>
      cases second with
      | words secondProof =>
          exact ListDerives.words
            (Derives.trans firstProof secondProof)

private theorem listDerives_of_perm_with_prefix
    (pre : List Nat) {xs ys : List Nat}
    (permutation : xs.Perm ys)
    (hlong : 3 ≤ (pre ++ xs).length) :
    ListDerives (pre ++ xs) (pre ++ ys) := by
  induction permutation generalizing pre with
  | nil =>
      cases pre with
      | nil => simp at hlong
      | cons p ps =>
          exact ListDerives.words (Derives.refl _)
  | cons x permutation ih =>
      have next :=
        ih (pre := pre ++ [x]) <| by
          simpa [List.append_assoc] using hlong
      simpa [List.append_assoc] using next
  | swap x y xs =>
      cases pre with
      | nil =>
          cases xs with
          | nil =>
              simp at hlong
          | cons z zs =>
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesPrefixSwap
                      (Word.singleton y) (Word.singleton x)
                      (wordOfCons z zs)
      | cons p ps =>
          cases xs with
          | nil =>
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using
                    derivesSuffixSwap
                      (wordOfCons p ps) (Word.singleton y)
                      (Word.singleton x)
          | cons z zs =>
              have swapped :=
                Derives.appendRight
                  (derivesSuffixSwap
                    (wordOfCons p ps) (Word.singleton y)
                    (Word.singleton x))
                  (wordOfCons z zs)
              exact ListDerives.words <| by
                simpa [wordOfCons, Word.singleton, Word.append,
                  Word.append_assoc] using swapped
  | trans first second ihFirst ihSecond =>
      have firstDerivation := ihFirst (pre := pre) hlong
      have secondDerivation :=
        ihSecond (pre := pre) <| by
          rw [List.length_append, ← first.length_eq]
          simpa [List.length_append] using hlong
      exact firstDerivation.trans secondDerivation

/-- Every permutation of a word of length at least three is derivable.
The theorem deliberately excludes words of length two. -/
theorem derivesLongPermutation (u v : Word Nat)
    (hlong : 3 ≤ u.toList.length)
    (permutation : u.toList.Perm v.toList) :
    Derives basis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          have lifted :=
            listDerives_of_perm_with_prefix []
              (xs := uHead :: uTail) (ys := vHead :: vTail)
              permutation hlong
          cases lifted with
          | words derivation =>
              exact derivation

/-- Every word of length at least three derives to its square. -/
theorem derivesSquare (w : Word Nat)
    (hlong : 3 ≤ w.toList.length) :
    Derives basis w (w ++ w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at hlong
      | cons next rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at hlong
          | cons third more =>
              let u := Word.singleton head
              let v₁ := Word.singleton next
              let v₂ := wordOfCons third more
              let v := v₁ ++ v₂
              have duplicateU := derivesLongDuplication u v₁ v₂
              have arrangeForV :
                  Derives basis (((u ++ u) ++ v₁) ++ v₂)
                    ((v ++ u) ++ u) :=
                derivesLongPermutation _ _ (by
                  simp [u, v₁, v₂, Word.toList]) <| by
                    rw [List.perm_iff_count]
                    intro z
                    simp only [Word.toList_append, List.count_append]
                    unfold v
                    simp only [Word.toList_append, List.count_append]
                    omega
              have duplicateV := derivesLongDuplication v u u
              have finish :
                  Derives basis (((v ++ v) ++ u) ++ u)
                    ((u ++ v) ++ (u ++ v)) :=
                derivesLongPermutation _ _ (by
                  simp [u, v, v₁, v₂, wordOfCons, Word.toList]
                  omega) <| by
                    rw [List.perm_iff_count]
                    intro z
                    simp only [Word.toList_append, List.count_append]
                    omega
              exact Derives.trans
                (by
                  simpa [u, v, v₁, v₂, wordOfCons,
                    Word.append_assoc] using duplicateU) <|
                Derives.trans arrangeForV <|
                Derives.trans duplicateV <| by
                  simpa [u, v, v₁, v₂, wordOfCons,
                    Word.append_assoc] using finish

/-- Every word of length at least three derives to its cube. -/
theorem derivesCube (w : Word Nat)
    (hlong : 3 ≤ w.toList.length) :
    Derives basis w ((w ++ w) ++ w) := by
  have square := derivesSquare w hlong
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at hlong
      | cons next rest =>
          let u := Word.singleton head
          let v := wordOfCons next rest
          have duplicateW :=
            derivesLongDuplication (wordOfCons head (next :: rest)) u v
          exact Derives.trans square <| by
            simpa [u, v, wordOfCons, Word.append_assoc] using duplicateW

private theorem four_copies_perm (x : Nat) (xs : List Nat)
    (hcount : 4 ≤ xs.count x) :
    xs.Perm
      (x :: x :: x :: x ::
        ((((xs.erase x).erase x).erase x).erase x)) := by
  have hx₀ : x ∈ xs :=
    List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx₀
  have hcount₁ : (xs.erase x).count x + 1 = xs.count x := by
    rw [List.count_erase_self]
    omega
  have hx₁ : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase hx₁
  have hcount₂ : ((xs.erase x).erase x).count x + 1 =
      (xs.erase x).count x := by
    rw [List.count_erase_self]
    omega
  have hx₂ : x ∈ (xs.erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have third := List.perm_cons_erase hx₂
  have hcount₃ : (((xs.erase x).erase x).erase x).count x + 1 =
      ((xs.erase x).erase x).count x := by
    rw [List.count_erase_self]
    omega
  have hx₃ : x ∈ ((xs.erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons x <|
    second.trans <| List.Perm.cons x <|
      third.trans <| List.Perm.cons x
        (List.perm_cons_erase hx₃)

private theorem contractLeadingFourList (x : Nat) (rest : List Nat) :
    Derives basis
      (wordOfCons x (x :: x :: x :: rest))
      (wordOfCons x (x :: x :: rest)) := by
  cases rest with
  | nil =>
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using
          derivesFourContraction (Word.singleton x)
  | cons y ys =>
      have contracted :=
        Derives.appendRight
          (derivesFourContraction (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.singleton, Word.append,
        Word.append_assoc] using contracted

private theorem derivesSaturatedCounts
    (x : Nat) (xs : List Nat)
    (hlong : 3 ≤ (x :: xs).length)
    (lower :
      ∀ z, z ∈ x :: xs → 3 ≤ (x :: xs).count z) :
    ∃ y ys,
      Derives basis (wordOfCons x xs) (wordOfCons y ys) ∧
      ∀ z, (y :: ys).count z =
        if z ∈ x :: xs then 3 else 0 := by
  classical
  by_cases capped : ∀ z, (x :: xs).count z ≤ 3
  · refine ⟨x, xs, Derives.refl _, ?_⟩
    intro z
    by_cases member : z ∈ x :: xs
    · rw [if_pos member]
      exact Nat.le_antisymm (capped z) (lower z member)
    · rw [if_neg member]
      exact List.count_eq_zero.mpr member
  · have existsLarge :
        ∃ z, 4 ≤ (x :: xs).count z := by
      apply Classical.byContradiction
      intro none
      apply capped
      intro z
      have notFour : ¬4 ≤ (x :: xs).count z := by
        intro four
        exact none ⟨z, four⟩
      omega
    obtain ⟨repeated, repeatedFour⟩ := existsLarge
    let rest :=
      (((((x :: xs).erase repeated).erase repeated).erase repeated).erase
        repeated)
    have arrangedPermutation :
        (x :: xs).Perm
          (repeated :: repeated :: repeated :: repeated :: rest) := by
      simpa [rest] using
        four_copies_perm repeated (x :: xs) repeatedFour
    have arrange :
        Derives basis (wordOfCons x xs)
          (wordOfCons repeated
            (repeated :: repeated :: repeated :: rest)) :=
      derivesLongPermutation _ _ hlong arrangedPermutation
    have contract :=
      contractLeadingFourList repeated rest
    have supportShorter (z : Nat) :
        z ∈ repeated :: repeated :: repeated :: rest ↔
          z ∈ x :: xs := by
      simpa using arrangedPermutation.mem_iff.symm
    have shorterLong :
        3 ≤ (repeated :: repeated :: repeated :: rest).length := by
      simp
    have shorterLower :
        ∀ z, z ∈ repeated :: repeated :: repeated :: rest →
          3 ≤ (repeated :: repeated :: repeated :: rest).count z := by
      intro z member
      by_cases hz : z = repeated
      · subst z
        simp
      · have sourceLower :=
          lower z ((supportShorter z).mp member)
        have countEq :=
          (List.perm_iff_count.mp arrangedPermutation) z
        simp only [List.count_cons_of_ne (Ne.symm hz)] at countEq
        simpa [List.count_cons_of_ne (Ne.symm hz)] using
          countEq ▸ sourceLower
    have shorterLess :
        (repeated :: repeated :: repeated :: rest).length <
          (x :: xs).length := by
      have lengths := arrangedPermutation.length_eq
      simp at lengths ⊢
      omega
    obtain ⟨y, ys, recursive, normalCounts⟩ :=
      derivesSaturatedCounts repeated
        (repeated :: repeated :: rest) shorterLong shorterLower
    refine ⟨y, ys,
      Derives.trans arrange (Derives.trans contract recursive), ?_⟩
    intro z
    rw [normalCounts]
    by_cases member :
        z ∈ repeated :: repeated :: repeated :: rest
    · rw [if_pos member, if_pos ((supportShorter z).mp member)]
    · rw [if_neg member, if_neg]
      intro sourceMember
      exact member ((supportShorter z).mpr sourceMember)
termination_by (x :: xs).length
decreasing_by exact shorterLess

/-- A long word derives to a word containing exactly three copies of every
supported variable and no unsupported variables. -/
theorem derivesLongNormal (w : Word Nat)
    (hlong : 3 ≤ w.toList.length) :
    ∃ y ys,
      Derives basis w (wordOfCons y ys) ∧
      ∀ z, (y :: ys).count z =
        if z ∈ w.toList then 3 else 0 := by
  have cube := derivesCube w hlong
  let cubed := (w ++ w) ++ w
  have cubedLong : 3 ≤ cubed.toList.length := by
    simp [cubed, Word.toList_append]
    omega
  have cubedLower :
      ∀ z, z ∈ cubed.toList → 3 ≤ cubed.toList.count z := by
    intro z member
    have originalMember : z ∈ w.toList := by
      simpa [cubed, Word.toList_append] using member
    have positive := List.count_pos_iff.mpr originalMember
    simp [cubed, Word.toList_append, List.count_append]
    omega
  cases hCubed : cubed with
  | mk head tail =>
      have cubedLong' : 3 ≤ (head :: tail).length := by
        simpa [hCubed, Word.toList] using cubedLong
      have cubedLower' :
          ∀ z, z ∈ head :: tail →
            3 ≤ (head :: tail).count z := by
        intro z member
        have member' : z ∈ cubed.toList := by
          simpa [hCubed, Word.toList] using member
        have lower' := cubedLower z member'
        simpa [hCubed, Word.toList] using lower'
      obtain ⟨y, ys, reduced, counts⟩ :=
        derivesSaturatedCounts head tail cubedLong' cubedLower'
      have reducedFromCubed :
          Derives basis cubed (wordOfCons y ys) := by
        simpa [hCubed, wordOfCons] using reduced
      refine ⟨y, ys,
        Derives.trans cube (by simpa [cubed] using reducedFromCubed), ?_⟩
      intro z
      rw [counts]
      have cubedSupport :
          z ∈ head :: tail ↔ z ∈ w.toList := by
        have support :
            z ∈ cubed.toList ↔ z ∈ w.toList := by
          simp [cubed, Word.toList_append]
        simpa [hCubed, Word.toList] using support
      simp only [cubedSupport]

/-- Long words with the same support are derivably equal. -/
theorem derivesLongOfSupportEq (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (support : ∀ z, z ∈ u.toList ↔ z ∈ v.toList) :
    Derives basis u v := by
  obtain ⟨ux, uxs, uNormal, uCounts⟩ :=
    derivesLongNormal u uLong
  obtain ⟨vx, vxs, vNormal, vCounts⟩ :=
    derivesLongNormal v vLong
  have normalPermutation :
      (ux :: uxs).Perm (vx :: vxs) := by
    rw [List.perm_iff_count]
    intro z
    rw [uCounts, vCounts]
    simp only [support z]
  have normalLong : 3 ≤ (ux :: uxs).length := by
    have headMember : u.head ∈ u.toList := List.Mem.head _
    have headCount := uCounts u.head
    rw [if_pos headMember] at headCount
    have countLe :=
      List.count_le_length (a := u.head) (l := ux :: uxs)
    omega
  exact Derives.trans uNormal <|
    Derives.trans
      (derivesLongPermutation
        (wordOfCons ux uxs) (wordOfCons vx vxs)
        normalLong normalPermutation)
      (Derives.symm vNormal)

/-- Two words have the same support when they contain exactly the same
variables, without regard to order or multiplicity. -/
def SameSupport (u v : Word Nat) : Prop :=
  ∀ z, z ∈ u.toList ↔ z ∈ v.toList

/-- The exact congruence generated by the `S5_199` basis: short words are
rigid, while words of length at least three are classified by support. -/
def ExactBasisClass (u v : Word Nat) : Prop :=
  u = v ∨
    (3 ≤ u.toList.length ∧
      3 ≤ v.toList.length ∧
      SameSupport u v)

private theorem sameSupport_refl (u : Word Nat) :
    SameSupport u u := by
  intro z
  rfl

private theorem sameSupport_symm {u v : Word Nat}
    (support : SameSupport u v) :
    SameSupport v u := by
  intro z
  exact (support z).symm

private theorem sameSupport_trans {u v w : Word Nat}
    (first : SameSupport u v)
    (second : SameSupport v w) :
    SameSupport u w := by
  intro z
  exact (first z).trans (second z)

private theorem exactBasisClass_symm {u v : Word Nat}
    (sameClass : ExactBasisClass u v) :
    ExactBasisClass v u := by
  rcases sameClass with equal | ⟨uLong, vLong, support⟩
  · exact Or.inl equal.symm
  · exact Or.inr ⟨vLong, uLong, sameSupport_symm support⟩

private theorem exactBasisClass_trans {u v w : Word Nat}
    (first : ExactBasisClass u v)
    (second : ExactBasisClass v w) :
    ExactBasisClass u w := by
  rcases first with equal | ⟨uLong, vLong, supportUV⟩
  · subst v
    exact second
  · rcases second with equal | ⟨vLong', wLong, supportVW⟩
    · subst w
      exact Or.inr ⟨uLong, vLong, supportUV⟩
    · exact Or.inr
        ⟨uLong, wLong, sameSupport_trans supportUV supportVW⟩

private theorem exactBasisClass_prepend (p : Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (p ++ u) (p ++ v) := by
  rcases sameClass with equal | ⟨uLong, vLong, support⟩
  · exact Or.inl (congrArg (fun w => p ++ w) equal)
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · simp only [Word.toList_append, List.length_append]
      omega
    · simp only [Word.toList_append, List.length_append]
      omega
    · intro z
      simp only [Word.toList_append, List.mem_append]
      constructor
      · rintro (inPrefix | inU)
        · exact Or.inl inPrefix
        · exact Or.inr ((support z).mp inU)
      · rintro (inPrefix | inV)
        · exact Or.inl inPrefix
        · exact Or.inr ((support z).mpr inV)

private theorem exactBasisClass_appendRight (q : Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (u ++ q) (v ++ q) := by
  rcases sameClass with equal | ⟨uLong, vLong, support⟩
  · exact Or.inl (congrArg (fun w => w ++ q) equal)
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · simp only [Word.toList_append, List.length_append]
      omega
    · simp only [Word.toList_append, List.length_append]
      omega
    · intro z
      simp only [Word.toList_append, List.mem_append]
      constructor
      · rintro (inU | inSuffix)
        · exact Or.inl ((support z).mp inU)
        · exact Or.inr inSuffix
      · rintro (inV | inSuffix)
        · exact Or.inl ((support z).mpr inV)
        · exact Or.inr inSuffix

private theorem list_length_le_flatMap_words
    (letters : List Nat) (substitution : Nat → Word Nat) :
    letters.length ≤
      (letters.flatMap fun letter => (substitution letter).toList).length := by
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have imagePositive : 1 ≤ (substitution letter).toList.length := by
        cases substitution letter
        simp [Word.toList]
      omega

private theorem bind_preserves_long
    (w : Word Nat) (substitution : Nat → Word Nat)
    (long : 3 ≤ w.toList.length) :
    3 ≤ (w.bind substitution).toList.length := by
  rw [Word.toList_bind]
  exact Nat.le_trans long
    (list_length_le_flatMap_words w.toList substitution)

private theorem bind_preserves_support
    {u v : Word Nat} (substitution : Nat → Word Nat)
    (support : SameSupport u v) :
    SameSupport (u.bind substitution) (v.bind substitution) := by
  intro z
  rw [Word.toList_bind, Word.toList_bind]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨x, inU, inImage⟩
    exact ⟨x, (support x).mp inU, inImage⟩
  · rintro ⟨x, inV, inImage⟩
    exact ⟨x, (support x).mpr inV, inImage⟩

private theorem exactBasisClass_subst
    (substitution : Nat → Word Nat)
    {u v : Word Nat} (sameClass : ExactBasisClass u v) :
    ExactBasisClass (u.bind substitution) (v.bind substitution) := by
  rcases sameClass with equal | ⟨uLong, vLong, support⟩
  · exact Or.inl (congrArg (fun w => w.bind substitution) equal)
  · exact Or.inr
      ⟨bind_preserves_long u substitution uLong,
        bind_preserves_long v substitution vLong,
        bind_preserves_support substitution support⟩

private theorem basis_member_exact
    (e : Identity Nat) (member : e ∈ basis) :
    ExactBasisClass e.lhs e.rhs := by
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ExactBasisClass, SameSupport, powerLaw, firstSwapLaw, transferLaw,
      prefixSwapLaw, heavyInsertionLaw, suffixCommutationLaw,
      prefixCommutationLaw, longInsertionLaw, xxx, xxxx, xxy, xyx, xyy,
      yxx, xxxy, xyz, xzy, yxz, xxyz, Word.toList] <;>
    intro z <;> omega

private theorem derives_exact {u v : Word Nat}
    (derivation : Derives basis u v) :
    ExactBasisClass u v := by
  induction derivation with
  | fromBasis member =>
      exact basis_member_exact _ member
  | refl =>
      exact Or.inl rfl
  | symm _ ih =>
      exact exactBasisClass_symm ih
  | trans _ _ ih₁ ih₂ =>
      exact exactBasisClass_trans ih₁ ih₂
  | prepend p _ ih =>
      exact exactBasisClass_prepend p ih
  | appendRight _ q ih =>
      exact exactBasisClass_appendRight q ih
  | subst _ substitution ih =>
      exact exactBasisClass_subst substitution ih

/-- Complete syntactic characterization of derivability from the published
eight identities (and hence from the reduced three-law core). -/
theorem derives_iff_exactBasisClass {u v : Word Nat} :
    Derives basis u v ↔ ExactBasisClass u v := by
  constructor
  · exact derives_exact
  · intro sameClass
    rcases sameClass with equal | ⟨uLong, vLong, support⟩
    · subst v
      exact Derives.refl _
    · exact derivesLongOfSupportEq u v uLong vLong support

/-- A valid quadratic identity with equal support is literal once the model
contains one ordered pair whose products differ in the two orders. -/
theorem validPair_eq_of_support_and_order
    (T : FiniteTable) (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    {a b c d : Nat}
    (valid :
      (Identity.mk (wordOfCons a [b]) (wordOfCons c [d])).SatisfiedBy
        T.semigroup)
    (support :
      ∀ z, z ∈ [a, b] ↔ z ∈ [c, d]) :
    a = c ∧ b = d := by
  by_cases hab : a = b
  · subst b
    have hc : c = a := by
      have member := (support c).mpr (by simp)
      simpa using member
    have hd : d = a := by
      have member := (support d).mpr (by simp)
      simpa using member
    subst c
    subst d
    exact ⟨rfl, rfl⟩
  · have hc : c = a ∨ c = b := by
      simpa using (support c).mpr (by simp)
    have hd : d = a ∨ d = b := by
      simpa using (support d).mpr (by simp)
    rcases hc with hc | hc
    · rcases hd with hd | hd
      · have bMember := (support b).mp (by simp)
        have hba : b = a := by
          simpa [hc, hd] using bMember
        exact False.elim (hab hba.symm)
      · exact ⟨hc.symm, hd.symm⟩
    · rcases hd with hd | hd
      · let valuation : Nat → Fin T.order :=
          fun z => if z = a then left else right
        have evaluated := valid valuation
        change
          T.mul (valuation a) (valuation b) =
            T.mul (valuation c) (valuation d) at evaluated
        rw [hc, hd] at evaluated
        have valueA : valuation a = left := by
          simp [valuation]
        have valueB : valuation b = right := by
          simp [valuation, Ne.symm hab]
        rw [valueA, valueB] at evaluated
        exact (orderNe evaluated).elim
      · have aMember := (support a).mp (by simp)
        have hab' : a = b := by
          simpa [hc, hd] using aMember
        exact False.elim (hab hab')

private theorem validLengthTwo_eq_of_support_and_order
    (T : FiniteTable) (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left)
    (e : Identity Nat) (valid : e.SatisfiedBy T.semigroup)
    (support :
      ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (lhsTwo : e.lhs.toList.length = 2)
    (rhsTwo : e.rhs.toList.length = 2) :
    e.lhs = e.rhs := by
  cases e with
  | mk lhs rhs =>
      cases lhs with
      | mk lx ltail =>
          cases ltail with
          | nil =>
              simp [Word.toList] at lhsTwo
          | cons ly lrest =>
              cases lrest with
              | nil =>
                  cases rhs with
                  | mk rx rtail =>
                      cases rtail with
                      | nil =>
                          simp [Word.toList] at rhsTwo
                      | cons ry rrest =>
                          cases rrest with
                          | nil =>
                              have coordinates :=
                                validPair_eq_of_support_and_order
                                  T left right orderNe valid <| by
                                    simpa [wordOfCons, Word.toList] using
                                      support
                              rcases coordinates with ⟨rfl, rfl⟩
                              rfl
                          | cons rz rzs =>
                              simp [Word.toList] at rhsTwo
              | cons lz lzs =>
                  simp [Word.toList] at lhsTwo

/-- Generic completeness theorem for the `S5_199` basis. A finite table only
has to model the basis, recover support and the length stratum capped at
three, and provide one noncommuting ordered pair. -/
theorem basis_complete_of_separates
    (T : FiniteTable)
    (modelsT : Models T.semigroup basis)
    (supportT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList)
    (cappedLengthT :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        min e.lhs.toList.length 3 =
          min e.rhs.toList.length 3)
    (left right : Fin T.order)
    (orderNe : T.mul left right ≠ T.mul right left) :
    BasisFor T.semigroup basis := by
  refine ⟨modelsT, ?_⟩
  intro e valid
  have support := supportT e valid
  have cappedLength := cappedLengthT e valid
  have lhsPositive : 0 < e.lhs.toList.length := by
    simp [Word.toList]
  have rhsPositive : 0 < e.rhs.toList.length := by
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      omega
    have lhsTail : e.lhs.tail = [] := by
      cases tailShape : e.lhs.tail with
      | nil => rfl
      | cons x xs =>
          have atLeastTwo : 2 ≤ e.lhs.toList.length := by
            simp [Word.toList, tailShape]
          omega
    have rhsTail : e.rhs.tail = [] := by
      cases tailShape : e.rhs.tail with
      | nil => rfl
      | cons x xs =>
          have atLeastTwo : 2 ≤ e.rhs.toList.length := by
            simp [Word.toList, tailShape]
          omega
    have headMember : e.lhs.head ∈ e.rhs.toList :=
      (support e.lhs.head).mp (List.Mem.head _)
    have heads : e.lhs.head = e.rhs.head := by
      simpa [Word.toList, rhsTail] using headMember
    have words : e.lhs = e.rhs := by
      apply Word.toList_injective
      simp [Word.toList, lhsTail, rhsTail, heads]
    rw [words]
    exact Derives.refl _
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        omega
      have words :=
        validLengthTwo_eq_of_support_and_order
          T left right orderNe e valid support lhsTwo rhsTwo
      rw [words]
      exact Derives.refl _
    · have lhsLong : 3 ≤ e.lhs.toList.length := by
        omega
      have rhsLong : 3 ≤ e.rhs.toList.length := by
        omega
      exact derivesLongOfSupportEq e.lhs e.rhs
        lhsLong rhsLong support

end SemigroupBasis.CoRoots.S5_199

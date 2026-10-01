import SemigroupBasis.Examples.CyclicThree
import SemigroupBasis.FiniteTable
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based table of the cyclic semigroup `C_{3,3}`. -/
def cyclicThreeThreeMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2
      else if b = 3 then 2 else 1
  else if a = 1 then
    if b = 0 then 1 else if b = 1 then 2 else if b = 2 then 0
      else if b = 3 then 0 else 2
  else if a = 2 then
    if b = 0 then 2 else if b = 1 then 0 else if b = 2 then 1
      else if b = 3 then 1 else 0
  else if a = 3 then
    if b = 0 then 2 else if b = 1 then 0 else if b = 2 then 1
      else if b = 3 then 1 else 0
  else
    if b = 0 then 1 else if b = 1 then 2 else if b = 2 then 0
      else if b = 3 then 0 else 3

/-- The five-element cyclic semigroup with index three and period three. -/
def cyclicThreeThree : FiniteTable where
  order := 5
  mul := cyclicThreeThreeMul
  assoc := by decide

def cyclicThreeThreeXY : Word Nat := ⟨0, [1]⟩
def cyclicThreeThreeYX : Word Nat := ⟨1, [0]⟩
def cyclicThreeThreeXXXYZT : Word Nat := ⟨0, [0, 0, 1, 2, 3]⟩
def cyclicThreeThreeYZT : Word Nat := ⟨1, [2, 3]⟩

def cyclicThreeThreeCommutativityLaw : Identity Nat :=
  ⟨cyclicThreeThreeXY, cyclicThreeThreeYX⟩

def cyclicThreeThreeLongCancellationLaw : Identity Nat :=
  ⟨cyclicThreeThreeXXXYZT, cyclicThreeThreeYZT⟩

/-- The basis `xy = yx`, `xxxyzt = yzt` for `C_{3,3}`. -/
def cyclicThreeThreeBasis : List (Identity Nat) :=
  [cyclicThreeThreeCommutativityLaw,
    cyclicThreeThreeLongCancellationLaw]

private def instantiateFourWords
    (u v w t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

theorem cyclicThreeThreeDerivesCommutativity (u v : Word Nat) :
    Derives cyclicThreeThreeBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicThreeThreeBasis
        cyclicThreeThreeXY cyclicThreeThreeYX :=
    Derives.fromBasis (e := cyclicThreeThreeCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateFourWords u v v v)
  simpa [cyclicThreeThreeBasis,
    cyclicThreeThreeCommutativityLaw, cyclicThreeThreeXY,
    cyclicThreeThreeYX, instantiateFourWords, Word.bind,
    Word.append, Word.singleton] using h

theorem cyclicThreeThreeDerivesCancelCube
    (u v w t : Word Nat) :
    Derives cyclicThreeThreeBasis
      (((((u ++ u) ++ u) ++ v) ++ w) ++ t) ((v ++ w) ++ t) := by
  have hbase :
      Derives cyclicThreeThreeBasis
        cyclicThreeThreeXXXYZT cyclicThreeThreeYZT :=
    Derives.fromBasis
      (e := cyclicThreeThreeLongCancellationLaw) <| by
        exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateFourWords u v w t)
  simpa [cyclicThreeThreeBasis,
    cyclicThreeThreeLongCancellationLaw, cyclicThreeThreeXXXYZT,
    cyclicThreeThreeYZT, instantiateFourWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicThreeThreeBasis
        (wordOfCons x xs) (wordOfCons y ys) →
      ListDerives (x :: xs) (y :: ys)

private theorem listDerives_of_perm {xs ys : List Nat}
    (h : xs.Perm ys) : ListDerives xs ys := by
  induction h with
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
              cyclicThreeThreeDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicThreeThreeDerivesCommutativity
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans _ _ ih₁ ih₂ =>
      cases ih₁ with
      | empty =>
          cases ih₂
          exact ListDerives.empty
      | words first =>
          cases ih₂ with
          | words second =>
              exact ListDerives.words (Derives.trans first second)

theorem cyclicThreeThreeDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicThreeThreeBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Equal exponent vectors modulo three are derivable in `C3`. This wrapper
exposes the syntactic part of the existing completeness proof for replay. -/
theorem cyclicThreeThreeDerivesCyclicModThree
    (u v : Word Nat)
    (modEq :
      ∀ z, u.toList.count z % 3 = v.toList.count z % 3) :
    Derives cyclicThreeBasis u v := by
  have reducedPerm :
      (ternaryReduce u.toList).Perm (ternaryReduce v.toList) :=
    ternaryReduce_perm_of_mod_eq modEq
  have lhsNormal := cyclicThreeDerivesNormal u
  have rhsNormal := cyclicThreeDerivesNormal v
  cases hl : ternaryReduce u.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : ternaryReduce v.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicThreeDerivesCommonCube
            (Word.singleton u.head) (Word.singleton v.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : ternaryReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (cyclicThreeDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

private theorem bind_append (u v : Word Nat) (σ : Nat → Word Nat) :
    (u ++ v).bind σ = u.bind σ ++ v.bind σ := by
  apply Word.toList_injective
  simp [Word.toList_bind]

private theorem bind_bind (w : Word Nat)
    (τ σ : Nat → Word Nat) :
    (w.bind τ).bind σ = w.bind (fun x => (τ x).bind σ) := by
  apply Word.toList_injective
  simp [Word.toList_bind, List.flatMap_assoc]

private theorem bind_singleton (w : Word Nat) :
    w.bind Word.singleton = w := by
  apply Word.toList_injective
  simp [Word.toList_bind]

/-- A `C3` derivation can be replayed after a product of three nonempty
words, which supplies the residual `yzt` context of the long law. -/
theorem cyclicThreeThreeLiftCyclic
    {u v : Word Nat}
    (h : Derives cyclicThreeBasis u v)
    (a b c : Word Nat) (σ : Nat → Word Nat) :
    Derives cyclicThreeThreeBasis
      (((a ++ b) ++ c) ++ u.bind σ)
      (((a ++ b) ++ c) ++ v.bind σ) := by
  induction h generalizing a b c σ with
  | fromBasis hmem =>
      simp only [cyclicThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · have commute :=
          cyclicThreeThreeDerivesCommutativity (σ 0) (σ 1)
        simpa [cyclicThreeCommutativityLaw, cyclicThreeXY,
          cyclicThreeYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend ((a ++ b) ++ c) commute
      · let marker := (a ++ b) ++ c
        let cube := (σ 0 ++ σ 0) ++ σ 0
        have enter :=
          Derives.appendRight
            (cyclicThreeThreeDerivesCommutativity marker cube) (σ 1)
        have cancel :=
          cyclicThreeThreeDerivesCancelCube
            (σ 0) a b (c ++ σ 1)
        exact Derives.trans
          (by
            simpa [cyclicThreeCancellationLaw, cyclicThreeXXXY,
              cyclicThreeY, marker, cube, Word.bind, Word.append,
              Word.singleton, Word.append_assoc] using enter)
          (by
            simpa [cyclicThreeCancellationLaw, cyclicThreeXXXY,
              cyclicThreeY, marker, Word.bind, Word.append,
              Word.singleton, Word.append_assoc] using cancel)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih a b c σ)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ a b c σ) (ih₂ a b c σ)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih a b (c ++ p.bind σ) σ
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih a b c σ) (q.bind σ)
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih a b c (fun x => (τ x).bind σ)

def cyclicThreeThreeMarkerLetter : Word Nat := Word.singleton 0

def cyclicThreeThreeMarker : Word Nat :=
  (cyclicThreeThreeMarkerLetter ++ cyclicThreeThreeMarkerLetter) ++
    cyclicThreeThreeMarkerLetter

theorem cyclicThreeThreeDerivesMarkerExpansion
    (w : Word Nat) (long : 3 ≤ w.toList.length) :
    Derives cyclicThreeThreeBasis
      w (cyclicThreeThreeMarker ++ w) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons next rest =>
          cases rest with
          | nil =>
              simp [Word.toList] at long
          | cons third remaining =>
              have inserted :=
                Derives.symm <|
                  cyclicThreeThreeDerivesCancelCube
                    cyclicThreeThreeMarkerLetter
                    (Word.singleton head) (Word.singleton next)
                    (wordOfCons third remaining)
              simpa [cyclicThreeThreeMarker,
                cyclicThreeThreeMarkerLetter, wordOfCons,
                Word.append, Word.singleton, Word.append_assoc] using
                  inserted

/-- Long words with equal exponent vectors modulo three are derivably equal. -/
theorem cyclicThreeThreeDerivesLongModThree
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (modEq :
      ∀ z, u.toList.count z % 3 = v.toList.count z % 3) :
    Derives cyclicThreeThreeBasis u v := by
  have expandedU := cyclicThreeThreeDerivesMarkerExpansion u uLong
  have expandedV := cyclicThreeThreeDerivesMarkerExpansion v vLong
  have cyclic :=
    cyclicThreeThreeDerivesCyclicModThree u v modEq
  have lifted :=
    cyclicThreeThreeLiftCyclic cyclic
      cyclicThreeThreeMarkerLetter cyclicThreeThreeMarkerLetter
      cyclicThreeThreeMarkerLetter Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact Derives.trans expandedU <|
    Derives.trans
      (by
        simpa [cyclicThreeThreeMarker, Word.append_assoc] using lifted)
      (Derives.symm expandedV)

/-- Deterministic ascending order for canonical exponent lists. -/
def cyclicThreeThreeSort (letters : List Nat) : List Nat :=
  letters.mergeSort (fun x y : Nat => decide (x ≤ y))

theorem cyclicThreeThreeSort_perm (letters : List Nat) :
    (cyclicThreeThreeSort letters).Perm letters := by
  exact List.mergeSort_perm _ _

/-- Prefix the fixed triple marker exactly when a ternary residue list has
length below the long-word threshold. -/
def cyclicThreeThreePadResidues (letters : List Nat) : List Nat :=
  if letters.length < 3 then [0, 0, 0] ++ letters else letters

theorem cyclicThreeThreePadResidues_length (letters : List Nat) :
    3 ≤ (cyclicThreeThreePadResidues letters).length := by
  unfold cyclicThreeThreePadResidues
  by_cases short : letters.length < 3
  · rw [if_pos short]
    simp
  · rw [if_neg short]
    omega

theorem cyclicThreeThreePadResidues_count_mod
    (z : Nat) (letters : List Nat) :
    (cyclicThreeThreePadResidues letters).count z % 3 =
      letters.count z % 3 := by
  unfold cyclicThreeThreePadResidues
  by_cases short : letters.length < 3
  · rw [if_pos short, List.count_append]
    have markerMod : [0, 0, 0].count z % 3 = 0 := by
      by_cases hz : z = 0
      · subst z
        decide
      · have hzero : 0 ≠ z := Ne.symm hz
        simp [hzero]
    rw [Nat.add_mod, markerMod]
    simp
  · rw [if_neg short]

/-- Short words use their sorted exact multiset. Long words use the sorted
ternary residue list, padded by the fixed triple marker when needed. -/
def cyclicThreeThreeCanonicalList (w : Word Nat) : List Nat :=
  if w.toList.length < 3 then
    cyclicThreeThreeSort w.toList
  else
    cyclicThreeThreePadResidues
      (cyclicThreeThreeSort (ternaryReduce w.toList))

private def wordOfList : List Nat → Word Nat
  | [] => Word.singleton 0
  | x :: xs => ⟨x, xs⟩

private theorem toList_wordOfList {letters : List Nat}
    (nonempty : letters ≠ []) :
    (wordOfList letters).toList = letters := by
  cases letters with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons x xs =>
      rfl

theorem cyclicThreeThreeCanonicalList_ne_nil (w : Word Nat) :
    cyclicThreeThreeCanonicalList w ≠ [] := by
  unfold cyclicThreeThreeCanonicalList
  split <;> rename_i short
  · intro empty
    have lengthEq :=
      (cyclicThreeThreeSort_perm w.toList).length_eq
    rw [empty] at lengthEq
    cases w with
    | mk head tail =>
        simp [Word.toList] at lengthEq
  · intro empty
    have longLength :=
      cyclicThreeThreePadResidues_length
        (cyclicThreeThreeSort (ternaryReduce w.toList))
    rw [empty] at longLength
    simp at longLength

def cyclicThreeThreeCanonicalWord (w : Word Nat) : Word Nat :=
  wordOfList (cyclicThreeThreeCanonicalList w)

theorem cyclicThreeThreeCanonicalWord_toList (w : Word Nat) :
    (cyclicThreeThreeCanonicalWord w).toList =
      cyclicThreeThreeCanonicalList w := by
  exact toList_wordOfList (cyclicThreeThreeCanonicalList_ne_nil w)

theorem cyclicThreeThreeCanonicalShort_perm
    (w : Word Nat) (short : w.toList.length < 3) :
    w.toList.Perm (cyclicThreeThreeCanonicalWord w).toList := by
  rw [cyclicThreeThreeCanonicalWord_toList,
    cyclicThreeThreeCanonicalList, if_pos short]
  exact (cyclicThreeThreeSort_perm w.toList).symm

theorem cyclicThreeThreeCanonicalLong_length
    (w : Word Nat) (long : 3 ≤ w.toList.length) :
    3 ≤ (cyclicThreeThreeCanonicalWord w).toList.length := by
  rw [cyclicThreeThreeCanonicalWord_toList,
    cyclicThreeThreeCanonicalList, if_neg (by omega)]
  exact cyclicThreeThreePadResidues_length _

theorem cyclicThreeThreeCanonicalLong_count_mod
    (w : Word Nat) (long : 3 ≤ w.toList.length) :
    ∀ z,
      (cyclicThreeThreeCanonicalWord w).toList.count z % 3 =
        w.toList.count z % 3 := by
  intro z
  rw [cyclicThreeThreeCanonicalWord_toList,
    cyclicThreeThreeCanonicalList, if_neg (by omega),
    cyclicThreeThreePadResidues_count_mod]
  have sortedCount :
      (cyclicThreeThreeSort (ternaryReduce w.toList)).count z =
        (ternaryReduce w.toList).count z :=
    List.perm_iff_count.mp
      (cyclicThreeThreeSort_perm (ternaryReduce w.toList)) z
  rw [sortedCount, count_ternaryReduce]
  omega

theorem cyclicThreeThreeDerivesCanonical (w : Word Nat) :
    Derives cyclicThreeThreeBasis w
      (cyclicThreeThreeCanonicalWord w) := by
  by_cases short : w.toList.length < 3
  · exact cyclicThreeThreeDerivesPermutation w
      (cyclicThreeThreeCanonicalWord w)
      (cyclicThreeThreeCanonicalShort_perm w short)
  · have long : 3 ≤ w.toList.length := by omega
    exact cyclicThreeThreeDerivesLongModThree w
      (cyclicThreeThreeCanonicalWord w) long
      (cyclicThreeThreeCanonicalLong_length w long)
      (fun z => (cyclicThreeThreeCanonicalLong_count_mod w long z).symm)

/-- The power state of the one-based generator `5`:
`5,4,1,2,3,1,2,3,...`. -/
def cyclicThreeThreeState (n : Nat) : Fin 5 :=
  if n = 1 then 4
  else if n = 2 then 3
  else if n % 3 = 0 then 0
  else if n % 3 = 1 then 1
  else 2

private theorem cyclicThreeThreeMul_state_one
    (n : Nat) (nPos : 0 < n) :
    cyclicThreeThreeMul (cyclicThreeThreeState n)
        (cyclicThreeThreeState 1) =
      cyclicThreeThreeState (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn0 : n ≠ 0 := by omega
      have hnext1 : n + 1 ≠ 1 := by omega
      have hnext2 : n + 1 ≠ 2 := by omega
      by_cases h0 : n % 3 = 0
      · have hnext : (n + 1) % 3 = 1 := by omega
        apply Fin.ext
        simp [cyclicThreeThreeState, cyclicThreeThreeMul, hn1,
          hn2, hn0, hnext1, hnext2, h0, hnext]
      · by_cases h1 : n % 3 = 1
        · have hnext : (n + 1) % 3 = 2 := by omega
          apply Fin.ext
          simp [cyclicThreeThreeState, cyclicThreeThreeMul, hn1,
            hn2, hn0, hnext1, hnext2, h0, h1, hnext]
        · have h2 : n % 3 = 2 := by omega
          have hnext : (n + 1) % 3 = 0 := by omega
          apply Fin.ext
          simp [cyclicThreeThreeState, cyclicThreeThreeMul, hn1,
            hn2, hn0, hnext1, hnext2, h0, h1, h2, hnext]

private theorem cyclicThreeThreeMul_state_two
    (n : Nat) (nPos : 0 < n) :
    cyclicThreeThreeMul (cyclicThreeThreeState n)
        (cyclicThreeThreeState 2) =
      cyclicThreeThreeState (n + 2) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hnext1 : n + 2 ≠ 1 := by omega
      have hnext2 : n + 2 ≠ 2 := by omega
      have hn0 : n ≠ 0 := by omega
      by_cases h0 : n % 3 = 0
      · have hnext : (n + 2) % 3 = 2 := by omega
        apply Fin.ext
        simp [cyclicThreeThreeState, cyclicThreeThreeMul, hn1,
          hn2, hn0, hnext1, hnext2, h0, hnext]
      · by_cases h1 : n % 3 = 1
        · have hnext : (n + 2) % 3 = 0 := by omega
          apply Fin.ext
          simp [cyclicThreeThreeState, cyclicThreeThreeMul, hn1,
            hn2, hn0, hnext1, hnext2, h0, h1, hnext]
        · have h2 : n % 3 = 2 := by omega
          have hnext : (n + 2) % 3 = 1 := by omega
          apply Fin.ext
          simp [cyclicThreeThreeState, cyclicThreeThreeMul, hn1,
            hn2, hn0, hnext1, hnext2, h0, h1, h2, hnext]

private def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => weight x + weightSum weight xs

private def weightedValuation (weight : Nat → Nat) : Nat → Fin 5 :=
  fun x => cyclicThreeThreeState (weight x)

private theorem cyclicThreeThreeFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current x =>
          cyclicThreeThreeMul current (weightedValuation weight x))
        (cyclicThreeThreeState acc) =
      cyclicThreeThreeState (acc + weightSum weight xs) := by
  induction xs generalizing acc with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo x with hx | hx
      · rw [show weightedValuation weight x =
            cyclicThreeThreeState 1 by simp [weightedValuation, hx]]
        rw [cyclicThreeThreeMul_state_one acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicThreeThreeMul current
                  (weightedValuation weight x))
              (cyclicThreeThreeState (acc + 1)) =
            cyclicThreeThreeState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 1) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega
      · rw [show weightedValuation weight x =
            cyclicThreeThreeState 2 by simp [weightedValuation, hx]]
        rw [cyclicThreeThreeMul_state_two acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicThreeThreeMul current
                  (weightedValuation weight x))
              (cyclicThreeThreeState (acc + 2)) =
            cyclicThreeThreeState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 2) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega

private theorem cyclicThreeThreeEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (w : Word Nat) :
    cyclicThreeThree.semigroup.eval (weightedValuation weight) w =
      cyclicThreeThreeState (weightSum weight w.toList) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicThreeThreeMul current
                (weightedValuation weight x))
            (weightedValuation weight head) =
          cyclicThreeThreeState
            (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          cyclicThreeThreeState (weight head) by rfl]
      have headPos : 0 < weight head := by
        rcases oneOrTwo head with h | h <;> omega
      rw [cyclicThreeThreeFold_weighted weight oneOrTwo tail
        (weight head) headPos]
      simp [weightSum]

private def unitWeight : Nat → Nat := fun _ => 1

private def doubledWeight (z : Nat) : Nat → Nat :=
  fun x => if x = z then 2 else 1

private theorem weightSum_unit (xs : List Nat) :
    weightSum unitWeight xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [weightSum, unitWeight, ih]
      omega

private theorem weightSum_doubled (z : Nat) (xs : List Nat) :
    weightSum (doubledWeight z) xs = xs.length + xs.count z := by
  induction xs with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      by_cases hx : x = z
      · subst x
        simp [weightSum, doubledWeight, ih]
        omega
      · simp [weightSum, doubledWeight, hx, ih]
        omega

theorem cyclicThreeThreeEval_unit (w : Word Nat) :
    cyclicThreeThree.semigroup.eval (weightedValuation unitWeight) w =
      cyclicThreeThreeState w.toList.length := by
  rw [cyclicThreeThreeEval_weighted unitWeight (by
    intro x
    exact Or.inl rfl)]
  rw [weightSum_unit]

theorem cyclicThreeThreeEval_doubled (z : Nat) (w : Word Nat) :
    cyclicThreeThree.semigroup.eval
        (weightedValuation (doubledWeight z)) w =
      cyclicThreeThreeState (w.toList.length + w.toList.count z) := by
  rw [cyclicThreeThreeEval_weighted (doubledWeight z) (by
    intro x
    by_cases hx : x = z
    · exact Or.inr (by simp [doubledWeight, hx])
    · exact Or.inl (by simp [doubledWeight, hx]))]
  rw [weightSum_doubled]

private theorem cyclicThreeThreeState_eq_one
    {n : Nat} (nPos : 0 < n) :
    cyclicThreeThreeState n = cyclicThreeThreeState 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · exact hn1
    · by_cases hn2 : n = 2
      · subst n
        simp [cyclicThreeThreeState] at h
      · by_cases h0 : n % 3 = 0
        · simp [cyclicThreeThreeState, hn1, hn2, h0] at h
        · by_cases h1 : n % 3 = 1
          · simp [cyclicThreeThreeState, hn1, hn2, h0, h1] at h
          · have h2 : n % 3 = 2 := by omega
            simp [cyclicThreeThreeState, hn1, hn2, h0, h1, h2] at h
  · intro h
    rw [h]

private theorem cyclicThreeThreeState_eq_two
    {n : Nat} (nPos : 0 < n) :
    cyclicThreeThreeState n = cyclicThreeThreeState 2 ↔ n = 2 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · subst n
      simp [cyclicThreeThreeState] at h
    · by_cases hn2 : n = 2
      · exact hn2
      · by_cases h0 : n % 3 = 0
        · simp [cyclicThreeThreeState, hn1, hn2, h0] at h
        · by_cases h1 : n % 3 = 1
          · simp [cyclicThreeThreeState, hn1, hn2, h0, h1] at h
          · have h2 : n % 3 = 2 := by omega
            simp [cyclicThreeThreeState, hn1, hn2, h0, h1, h2] at h
  · intro h
    rw [h]

private theorem cyclicThreeThreeState_long_mod_three
    {m n : Nat} (mLong : 3 ≤ m) (nLong : 3 ≤ n)
    (h : cyclicThreeThreeState m = cyclicThreeThreeState n) :
    m % 3 = n % 3 := by
  have hm1 : m ≠ 1 := by omega
  have hm2 : m ≠ 2 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;>
    rcases hn with hn | hn | hn
  · omega
  · simp [cyclicThreeThreeState, hm1, hm2, hn1, hn2, hm, hn] at h
  · simp [cyclicThreeThreeState, hm1, hm2, hn1, hn2, hm, hn] at h
  · simp [cyclicThreeThreeState, hm1, hm2, hn1, hn2, hm, hn] at h
  · omega
  · simp [cyclicThreeThreeState, hm1, hm2, hn1, hn2, hm, hn] at h
  · simp [cyclicThreeThreeState, hm1, hm2, hn1, hn2, hm, hn] at h
  · simp [cyclicThreeThreeState, hm1, hm2, hn1, hn2, hm, hn] at h
  · omega

private theorem cyclicThreeThreeState_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (h :
      cyclicThreeThreeState (1 + m) =
        cyclicThreeThreeState (1 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 := by omega
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hm with rfl | rfl <;>
    rcases hn with rfl | rfl <;>
    simp [cyclicThreeThreeState] at h ⊢

private theorem cyclicThreeThreeState_two_add_injective
    {m n : Nat} (mLe : m ≤ 2) (nLe : n ≤ 2)
    (h :
      cyclicThreeThreeState (2 + m) =
        cyclicThreeThreeState (2 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hm with rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl <;>
    simp [cyclicThreeThreeState] at h ⊢

def cyclicThreeThreeFiniteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def cyclicThreeThreeFiniteLongCancellationLaw : Identity (Fin 4) :=
  ⟨⟨0, [0, 0, 1, 2, 3]⟩, ⟨1, [2, 3]⟩⟩

theorem cyclicThreeThreeFiniteCommutativityLaw_map :
    cyclicThreeThreeFiniteCommutativityLaw.map Fin.val =
      cyclicThreeThreeCommutativityLaw := rfl

theorem cyclicThreeThreeFiniteLongCancellationLaw_map :
    cyclicThreeThreeFiniteLongCancellationLaw.map Fin.val =
      cyclicThreeThreeLongCancellationLaw := rfl

set_option maxRecDepth 100000 in
theorem cyclicThreeThreeBasis_models :
    Models cyclicThreeThree.semigroup cyclicThreeThreeBasis := by
  intro e he
  simp only [cyclicThreeThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← cyclicThreeThreeFiniteCommutativityLaw_map]
    exact cyclicThreeThree.checkIdentityNat_sound
      cyclicThreeThreeFiniteCommutativityLaw (by decide)
  · rw [← cyclicThreeThreeFiniteLongCancellationLaw_map]
    exact cyclicThreeThree.checkIdentityNat_sound
      cyclicThreeThreeFiniteLongCancellationLaw (by decide)

/-- Unrestricted completeness over `Nat` variables. Lengths one and two retain
their exact commutative multisets. At length at least three, the weighted
evaluations recover the exponent vector modulo three. -/
theorem cyclicThreeThreeBasis_complete :
    BasisFor cyclicThreeThree.semigroup cyclicThreeThreeBasis := by
  refine ⟨cyclicThreeThreeBasis_models, ?_⟩
  intro e valid
  have lengthState :
      cyclicThreeThreeState e.lhs.toList.length =
        cyclicThreeThreeState e.rhs.toList.length := by
    have evaluated := valid (weightedValuation unitWeight)
    rw [cyclicThreeThreeEval_unit,
      cyclicThreeThreeEval_unit] at evaluated
    exact evaluated
  have weightedState :
      ∀ z,
        cyclicThreeThreeState
            (e.lhs.toList.length + e.lhs.toList.count z) =
          cyclicThreeThreeState
            (e.rhs.toList.length + e.rhs.toList.count z) := by
    intro z
    have evaluated := valid (weightedValuation (doubledWeight z))
    rw [cyclicThreeThreeEval_doubled,
      cyclicThreeThreeEval_doubled] at evaluated
    exact evaluated
  have lhsPos : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      apply (cyclicThreeThreeState_eq_one rhsPos).mp
      rw [← lengthState, lhsOne]
    have countEq : ∀ z,
        e.lhs.toList.count z = e.rhs.toList.count z := by
      intro z
      apply cyclicThreeThreeState_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length (a := z) (l := e.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length (a := z) (l := e.rhs.toList))
      · simpa [lhsOne, rhsOne] using weightedState z
    exact cyclicThreeThreeDerivesPermutation e.lhs e.rhs <|
      List.perm_iff_count.mpr countEq
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        apply (cyclicThreeThreeState_eq_two rhsPos).mp
        rw [← lengthState, lhsTwo]
      have countEq : ∀ z,
          e.lhs.toList.count z = e.rhs.toList.count z := by
        intro z
        apply cyclicThreeThreeState_two_add_injective
        · simpa [lhsTwo] using
            (List.count_le_length (a := z) (l := e.lhs.toList))
        · simpa [rhsTwo] using
            (List.count_le_length (a := z) (l := e.rhs.toList))
        · simpa [lhsTwo, rhsTwo] using weightedState z
      exact cyclicThreeThreeDerivesPermutation e.lhs e.rhs <|
        List.perm_iff_count.mpr countEq
    · have lhsLong : 3 ≤ e.lhs.toList.length := by omega
      have rhsNotOne : e.rhs.toList.length ≠ 1 := by
        intro rhsOne
        have lhsStateOne :
            cyclicThreeThreeState e.lhs.toList.length =
              cyclicThreeThreeState 1 := by
          rw [lengthState, rhsOne]
        exact lhsOne <|
          (cyclicThreeThreeState_eq_one lhsPos).mp lhsStateOne
      have rhsNotTwo : e.rhs.toList.length ≠ 2 := by
        intro rhsTwo
        have lhsStateTwo :
            cyclicThreeThreeState e.lhs.toList.length =
              cyclicThreeThreeState 2 := by
          rw [lengthState, rhsTwo]
        exact lhsTwo <|
          (cyclicThreeThreeState_eq_two lhsPos).mp lhsStateTwo
      have rhsLong : 3 ≤ e.rhs.toList.length := by omega
      have lengthMod :
          e.lhs.toList.length % 3 =
            e.rhs.toList.length % 3 :=
        cyclicThreeThreeState_long_mod_three
          lhsLong rhsLong lengthState
      have modEq :
          ∀ z,
            e.lhs.toList.count z % 3 =
              e.rhs.toList.count z % 3 := by
        intro z
        have totalMod :=
          cyclicThreeThreeState_long_mod_three
            (m := e.lhs.toList.length + e.lhs.toList.count z)
            (n := e.rhs.toList.length + e.rhs.toList.count z)
            (by omega) (by omega) (weightedState z)
        rw [Nat.add_mod, Nat.add_mod] at totalMod
        omega
      exact cyclicThreeThreeDerivesLongModThree
        e.lhs e.rhs lhsLong rhsLong modEq

theorem cyclicThreeThree_selfDual :
    cyclicThreeThree.semigroup.opposite =
      cyclicThreeThree.semigroup := by
  unfold cyclicThreeThree FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem cyclicThreeThreeOppositeBasis_complete :
    BasisFor cyclicThreeThree.semigroup.opposite
      cyclicThreeThreeBasis := by
  rw [cyclicThreeThree_selfDual]
  exact cyclicThreeThreeBasis_complete

end SemigroupBasis.Examples

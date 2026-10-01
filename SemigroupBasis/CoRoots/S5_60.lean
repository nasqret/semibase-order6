import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.FiniteTable
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_60

open SemigroupBasis
open SemigroupBasis.Examples

/-- The zero-based table of the cyclic semigroup `C_{4,2}`:
`[[1,1,3,3,3],[1,1,3,3,4],[3,3,1,1,1],[3,3,1,1,1],
[3,4,1,1,2]]`. -/
def cyclicFourTwoMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2
      else if b = 3 then 2 else 2
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2
      else if b = 3 then 2 else 3
  else if a = 2 then
    if b = 0 then 2 else if b = 1 then 2 else if b = 2 then 0
      else if b = 3 then 0 else 0
  else if a = 3 then
    if b = 0 then 2 else if b = 1 then 2 else if b = 2 then 0
      else if b = 3 then 0 else 0
  else if b = 0 then 2 else if b = 1 then 3 else if b = 2 then 0
    else if b = 3 then 0 else 1

/-- The five-element cyclic semigroup with index four and period two. -/
def cyclicFourTwo : FiniteTable where
  order := 5
  mul := cyclicFourTwoMul
  assoc := by decide

def cyclicFourTwoXY : Word Nat := ⟨0, [1]⟩
def cyclicFourTwoYX : Word Nat := ⟨1, [0]⟩
def cyclicFourTwoXXYZTU : Word Nat := ⟨0, [0, 1, 2, 3, 4]⟩
def cyclicFourTwoYZTU : Word Nat := ⟨1, [2, 3, 4]⟩

def cyclicFourTwoCommutativityLaw : Identity Nat :=
  ⟨cyclicFourTwoXY, cyclicFourTwoYX⟩

def cyclicFourTwoLongCancellationLaw : Identity Nat :=
  ⟨cyclicFourTwoXXYZTU, cyclicFourTwoYZTU⟩

/-- The basis `xy = yx`, `xxyztu = yztu` for `C_{4,2}`. -/
def cyclicFourTwoBasis : List (Identity Nat) :=
  [cyclicFourTwoCommutativityLaw, cyclicFourTwoLongCancellationLaw]

abbrev basis : List (Identity Nat) := cyclicFourTwoBasis

private def instantiateFiveWords
    (u v w t q : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => t
  | 4 => q
  | n + 5 => Word.singleton (n + 5)

theorem cyclicFourTwoDerivesCommutativity (u v : Word Nat) :
    Derives cyclicFourTwoBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicFourTwoBasis cyclicFourTwoXY cyclicFourTwoYX :=
    Derives.fromBasis (e := cyclicFourTwoCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateFiveWords u v v v v)
  simpa [cyclicFourTwoBasis, cyclicFourTwoCommutativityLaw,
    cyclicFourTwoXY, cyclicFourTwoYX, instantiateFiveWords, Word.bind,
    Word.append, Word.singleton] using h

theorem cyclicFourTwoDerivesCancelSquare
    (u v w t q : Word Nat) :
    Derives cyclicFourTwoBasis
      (((((u ++ u) ++ v) ++ w) ++ t) ++ q)
      (((v ++ w) ++ t) ++ q) := by
  have hbase :
      Derives cyclicFourTwoBasis
        cyclicFourTwoXXYZTU cyclicFourTwoYZTU :=
    Derives.fromBasis (e := cyclicFourTwoLongCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateFiveWords u v w t q)
  simpa [cyclicFourTwoBasis, cyclicFourTwoLongCancellationLaw,
    cyclicFourTwoXXYZTU, cyclicFourTwoYZTU, instantiateFiveWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicFourTwoBasis
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
              cyclicFourTwoDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicFourTwoDerivesCommutativity
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

theorem cyclicFourTwoDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicFourTwoBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

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

/-- Equal exponent-parity vectors are exactly the derivable identities of the
`C₂` basis. This local copy keeps the released `CyclicTwo` proof source
immutable while allowing the `C_{4,2}` argument to replay the derivation. -/
theorem cyclicFourTwoDerivesCyclicParity (u v : Word Nat)
    (parityEq :
      ∀ z, u.toList.count z % 2 = v.toList.count z % 2) :
    Derives cyclicTwoBasis u v := by
  have reducedPerm :
      (parityReduce u.toList).Perm (parityReduce v.toList) :=
    parityReduce_perm_of_parity_eq parityEq
  have lhsNormal := cyclicDerivesNormal u
  have rhsNormal := cyclicDerivesNormal v
  cases hl : parityReduce u.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : parityReduce v.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicDerivesCommonSquare
            (Word.singleton u.head) (Word.singleton v.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : parityReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (cyclicDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

/-- A derivation for `C₂` can be replayed after any fixed product of four
nonempty words. That product supplies the residual `yztu` context required by
`xxyztu = yztu`. -/
theorem cyclicFourTwoLiftCyclic
    {u v : Word Nat}
    (h : Derives cyclicTwoBasis u v)
    (a b c d : Word Nat) (σ : Nat → Word Nat) :
    Derives cyclicFourTwoBasis
      ((((a ++ b) ++ c) ++ d) ++ u.bind σ)
      ((((a ++ b) ++ c) ++ d) ++ v.bind σ) := by
  induction h generalizing a b c d σ with
  | fromBasis hmem =>
      simp only [cyclicTwoBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · have commute :=
          cyclicFourTwoDerivesCommutativity (σ 0) (σ 1)
        simpa [cyclicCommutativityLaw, cyclicXY, cyclicYX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend (((a ++ b) ++ c) ++ d) commute
      · let marker := ((a ++ b) ++ c) ++ d
        let square := σ 0 ++ σ 0
        have enter :=
          Derives.appendRight
            (cyclicFourTwoDerivesCommutativity marker square) (σ 1)
        have cancel :=
          cyclicFourTwoDerivesCancelSquare (σ 0) a b c (d ++ σ 1)
        exact Derives.trans
          (by
            simpa [cyclicCancellationLaw, cyclicXXY, cyclicY,
              marker, square, Word.bind, Word.append, Word.singleton,
              Word.append_assoc] using enter)
          (by
            simpa [cyclicCancellationLaw, cyclicXXY, cyclicY,
              marker, Word.bind, Word.append, Word.singleton,
              Word.append_assoc] using cancel)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih a b c d σ)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ a b c d σ) (ih₂ a b c d σ)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih a b c (d ++ p.bind σ) σ
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih a b c d σ) (q.bind σ)
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih a b c d (fun x => (τ x).bind σ)

private def markerLetter : Word Nat := Word.singleton 0

private def parityMarker : Word Nat :=
  ((markerLetter ++ markerLetter) ++ markerLetter) ++ markerLetter

private theorem cyclicFourTwoDerivesMarkerExpansion
    (w : Word Nat) (long : 4 ≤ w.toList.length) :
    Derives cyclicFourTwoBasis
      w (parityMarker ++ (parityMarker ++ w)) := by
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
              cases remaining with
              | nil =>
                  simp [Word.toList] at long
              | cons fourth suffix =>
                  have inserted :=
                    Derives.symm <|
                      cyclicFourTwoDerivesCancelSquare parityMarker
                        (Word.singleton head) (Word.singleton next)
                        (Word.singleton third) (wordOfCons fourth suffix)
                  simpa [parityMarker, markerLetter, wordOfCons,
                    Word.append, Word.singleton, Word.append_assoc] using
                      inserted

/-- Long words with equal exponent parities are derivably equal. -/
theorem cyclicFourTwoDerivesLongParity
    (u v : Word Nat)
    (uLong : 4 ≤ u.toList.length)
    (vLong : 4 ≤ v.toList.length)
    (parityEq :
      ∀ z, u.toList.count z % 2 = v.toList.count z % 2) :
    Derives cyclicFourTwoBasis u v := by
  have expandedU := cyclicFourTwoDerivesMarkerExpansion u uLong
  have expandedV := cyclicFourTwoDerivesMarkerExpansion v vLong
  have markedParity :
      ∀ z,
        (parityMarker ++ u).toList.count z % 2 =
          (parityMarker ++ v).toList.count z % 2 := by
    intro z
    simp only [Word.toList_append, List.count_append]
    rw [Nat.add_mod, Nat.add_mod, parityEq z]
    omega
  have cyclic :=
    cyclicFourTwoDerivesCyclicParity
      (parityMarker ++ u) (parityMarker ++ v)
      markedParity
  have lifted :=
    cyclicFourTwoLiftCyclic cyclic
      markerLetter markerLetter markerLetter markerLetter Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact Derives.trans expandedU <|
    Derives.trans
      (by
        simpa [parityMarker, Word.append_assoc] using lifted)
      (Derives.symm expandedV)

/-- The state of the power `aⁿ`, where zero-based element `4` is the
generator: `a, a², a³, a⁴, a⁵, ... = 4,1,3,0,2,0,2,...`. -/
private def cyclicFourTwoState (n : Nat) : Fin 5 :=
  if n = 1 then 4
  else if n = 2 then 1
  else if n = 3 then 3
  else if n % 2 = 0 then 0
  else 2

private theorem cyclicFourTwoMul_state_one
    (n : Nat) (nPos : 0 < n) :
    cyclicFourTwoMul (cyclicFourTwoState n)
        (cyclicFourTwoState 1) =
      cyclicFourTwoState (n + 1) := by
  have hn0 : n ≠ 0 := by omega
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hn3 : n = 3
      · subst n
        rfl
      · have hnext1 : n + 1 ≠ 1 := by omega
        have hnext2 : n + 1 ≠ 2 := by omega
        have hnext3 : n + 1 ≠ 3 := by omega
        by_cases hnEven : n % 2 = 0
        · have hnext : (n + 1) % 2 = 1 := by omega
          apply Fin.ext
          simp [cyclicFourTwoState, cyclicFourTwoMul,
            hn0, hn1, hn2, hn3, hnext1, hnext2, hnext3, hnEven, hnext]
        · have hnOdd : n % 2 = 1 := by omega
          have hnext : (n + 1) % 2 = 0 := by omega
          apply Fin.ext
          simp [cyclicFourTwoState, cyclicFourTwoMul,
            hn0, hn1, hn2, hn3, hnext1, hnext2, hnext3, hnOdd, hnext]

private theorem cyclicFourTwoMul_state_two
    (n : Nat) (nPos : 0 < n) :
    cyclicFourTwoMul (cyclicFourTwoState n)
        (cyclicFourTwoState 2) =
      cyclicFourTwoState (n + 2) := by
  have hn0 : n ≠ 0 := by omega
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hn3 : n = 3
      · subst n
        rfl
      · have hnext1 : n + 2 ≠ 1 := by omega
        have hnext2 : n + 2 ≠ 2 := by omega
        have hnext3 : n + 2 ≠ 3 := by omega
        by_cases hnEven : n % 2 = 0
        · have hnext : (n + 2) % 2 = 0 := by omega
          apply Fin.ext
          simp [cyclicFourTwoState, cyclicFourTwoMul,
            hn0, hn1, hn2, hn3, hnext1, hnext2, hnext3, hnEven, hnext]
        · have hnOdd : n % 2 = 1 := by omega
          have hnext : (n + 2) % 2 = 1 := by omega
          apply Fin.ext
          simp [cyclicFourTwoState, cyclicFourTwoMul,
            hn0, hn1, hn2, hn3, hnext1, hnext2, hnext3, hnOdd, hnext]

private def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => weight x + weightSum weight xs

private def weightedValuation (weight : Nat → Nat) : Nat → Fin 5 :=
  fun x => cyclicFourTwoState (weight x)

private theorem cyclicFourTwoFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current x =>
          cyclicFourTwoMul current (weightedValuation weight x))
        (cyclicFourTwoState acc) =
      cyclicFourTwoState (acc + weightSum weight xs) := by
  induction xs generalizing acc with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo x with hx | hx
      · rw [show weightedValuation weight x =
            cyclicFourTwoState 1 by simp [weightedValuation, hx]]
        rw [cyclicFourTwoMul_state_one acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicFourTwoMul current (weightedValuation weight x))
              (cyclicFourTwoState (acc + 1)) =
            cyclicFourTwoState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 1) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega
      · rw [show weightedValuation weight x =
            cyclicFourTwoState 2 by simp [weightedValuation, hx]]
        rw [cyclicFourTwoMul_state_two acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicFourTwoMul current (weightedValuation weight x))
              (cyclicFourTwoState (acc + 2)) =
            cyclicFourTwoState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 2) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega

private theorem cyclicFourTwoEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (w : Word Nat) :
    cyclicFourTwo.semigroup.eval (weightedValuation weight) w =
      cyclicFourTwoState (weightSum weight w.toList) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicFourTwoMul current (weightedValuation weight x))
            (weightedValuation weight head) =
          cyclicFourTwoState
            (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          cyclicFourTwoState (weight head) by rfl]
      have headPos : 0 < weight head := by
        rcases oneOrTwo head with h | h <;> omega
      rw [cyclicFourTwoFold_weighted weight oneOrTwo tail
        (weight head) headPos]
      simp [weightSum]

private def unitWeight : Nat → Nat := fun _ => 1

private def doubledWeight (z : Nat) : Nat → Nat :=
  fun x => if x = z then 2 else 1

private def complementedWeight (z : Nat) : Nat → Nat :=
  fun x => if x = z then 1 else 2

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

private theorem weightSum_complemented (z : Nat) (xs : List Nat) :
    weightSum (complementedWeight z) xs =
      2 * xs.length - xs.count z := by
  induction xs with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      have countLe := List.count_le_length (a := z) (l := xs)
      by_cases hx : x = z
      · subst x
        simp [weightSum, complementedWeight, ih]
        omega
      · simp [weightSum, complementedWeight, hx, ih]
        omega

private theorem cyclicFourTwoEval_unit (w : Word Nat) :
    cyclicFourTwo.semigroup.eval (weightedValuation unitWeight) w =
      cyclicFourTwoState w.toList.length := by
  rw [cyclicFourTwoEval_weighted unitWeight (by
    intro x
    exact Or.inl rfl)]
  rw [weightSum_unit]

private theorem cyclicFourTwoEval_doubled (z : Nat) (w : Word Nat) :
    cyclicFourTwo.semigroup.eval (weightedValuation (doubledWeight z)) w =
      cyclicFourTwoState (w.toList.length + w.toList.count z) := by
  rw [cyclicFourTwoEval_weighted (doubledWeight z) (by
    intro x
    by_cases hx : x = z
    · exact Or.inr (by simp [doubledWeight, hx])
    · exact Or.inl (by simp [doubledWeight, hx]))]
  rw [weightSum_doubled]

private theorem cyclicFourTwoEval_complemented (z : Nat) (w : Word Nat) :
    cyclicFourTwo.semigroup.eval
        (weightedValuation (complementedWeight z)) w =
      cyclicFourTwoState
        (2 * w.toList.length - w.toList.count z) := by
  rw [cyclicFourTwoEval_weighted (complementedWeight z) (by
    intro x
    by_cases hx : x = z
    · exact Or.inl (by simp [complementedWeight, hx])
    · exact Or.inr (by simp [complementedWeight, hx]))]
  rw [weightSum_complemented]

private theorem cyclicFourTwoState_eq_one
    {n : Nat} (nPos : 0 < n) :
    cyclicFourTwoState n = cyclicFourTwoState 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · exact hn1
    · by_cases hn2 : n = 2
      · subst n
        simp [cyclicFourTwoState] at h
      · by_cases hn3 : n = 3
        · subst n
          simp [cyclicFourTwoState] at h
        · by_cases hnEven : n % 2 = 0
          · simp [cyclicFourTwoState, hn1, hn2, hn3, hnEven] at h
          · simp [cyclicFourTwoState, hn1, hn2, hn3, hnEven] at h
  · intro h
    rw [h]

private theorem cyclicFourTwoState_eq_two
    {n : Nat} (nPos : 0 < n) :
    cyclicFourTwoState n = cyclicFourTwoState 2 ↔ n = 2 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · subst n
      simp [cyclicFourTwoState] at h
    · by_cases hn2 : n = 2
      · exact hn2
      · by_cases hn3 : n = 3
        · subst n
          simp [cyclicFourTwoState] at h
        · by_cases hnEven : n % 2 = 0
          · simp [cyclicFourTwoState, hn1, hn2, hn3, hnEven] at h
          · simp [cyclicFourTwoState, hn1, hn2, hn3, hnEven] at h
  · intro h
    rw [h]

private theorem cyclicFourTwoState_eq_three
    {n : Nat} (nPos : 0 < n) :
    cyclicFourTwoState n = cyclicFourTwoState 3 ↔ n = 3 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · subst n
      simp [cyclicFourTwoState] at h
    · by_cases hn2 : n = 2
      · subst n
        simp [cyclicFourTwoState] at h
      · by_cases hn3 : n = 3
        · exact hn3
        · by_cases hnEven : n % 2 = 0
          · simp [cyclicFourTwoState, hn1, hn2, hn3, hnEven] at h
          · simp [cyclicFourTwoState, hn1, hn2, hn3, hnEven] at h
  · intro h
    rw [h]

private theorem cyclicFourTwoState_long_parity
    {m n : Nat} (mLong : 4 ≤ m) (nLong : 4 ≤ n)
    (h : cyclicFourTwoState m = cyclicFourTwoState n) :
    m % 2 = n % 2 := by
  have hm1 : m ≠ 1 := by omega
  have hm2 : m ≠ 2 := by omega
  have hm3 : m ≠ 3 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hn3 : n ≠ 3 := by omega
  by_cases hmEven : m % 2 = 0
  · by_cases hnEven : n % 2 = 0
    · exact hmEven.trans hnEven.symm
    · have hnOdd : n % 2 = 1 := by omega
      simp [cyclicFourTwoState, hm1, hm2, hm3, hn1, hn2, hn3,
        hmEven, hnEven] at h
  · have hmOdd : m % 2 = 1 := by omega
    by_cases hnEven : n % 2 = 0
    · simp [cyclicFourTwoState, hm1, hm2, hm3, hn1, hn2, hn3,
        hmEven, hnEven] at h
    · have hnOdd : n % 2 = 1 := by omega
      exact hmOdd.trans hnOdd.symm

private theorem cyclicFourTwoState_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (h :
      cyclicFourTwoState (1 + m) =
        cyclicFourTwoState (1 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 := by omega
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hm with rfl | rfl <;>
    rcases hn with rfl | rfl <;>
    simp [cyclicFourTwoState] at h ⊢

private theorem cyclicFourTwoState_two_add_injective
    {m n : Nat} (mLe : m ≤ 2) (nLe : n ≤ 2)
    (h :
      cyclicFourTwoState (2 + m) =
        cyclicFourTwoState (2 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hm with rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl <;>
    simp [cyclicFourTwoState] at h ⊢

private theorem cyclicFourTwoState_three_count_injective
    {m n : Nat} (mLe : m ≤ 3) (nLe : n ≤ 3)
    (doubled :
      cyclicFourTwoState (3 + m) =
        cyclicFourTwoState (3 + n))
    (complemented :
      cyclicFourTwoState (6 - m) =
        cyclicFourTwoState (6 - n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hm with rfl | rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl | rfl <;>
    simp [cyclicFourTwoState] at doubled complemented ⊢

def cyclicFourTwoFiniteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def cyclicFourTwoFiniteLongCancellationLaw : Identity (Fin 5) :=
  ⟨⟨0, [0, 1, 2, 3, 4]⟩, ⟨1, [2, 3, 4]⟩⟩

theorem cyclicFourTwoFiniteCommutativityLaw_map :
    cyclicFourTwoFiniteCommutativityLaw.map Fin.val =
      cyclicFourTwoCommutativityLaw := rfl

theorem cyclicFourTwoFiniteLongCancellationLaw_map :
    cyclicFourTwoFiniteLongCancellationLaw.map Fin.val =
      cyclicFourTwoLongCancellationLaw := rfl

set_option maxRecDepth 100000 in
theorem cyclicFourTwoBasis_models :
    Models cyclicFourTwo.semigroup cyclicFourTwoBasis := by
  intro e he
  simp only [cyclicFourTwoBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← cyclicFourTwoFiniteCommutativityLaw_map]
    exact cyclicFourTwo.checkIdentityNat_sound
      cyclicFourTwoFiniteCommutativityLaw (by decide)
  · rw [← cyclicFourTwoFiniteLongCancellationLaw_map]
    exact cyclicFourTwo.checkIdentityNat_sound
      cyclicFourTwoFiniteLongCancellationLaw (by decide)

/-- Unrestricted completeness over `Nat` variables. Lengths one through three
retain their exact commutative multisets. At length at least four, weighted
evaluations recover only the exponent-parity vector, and the contextual `C₂`
replay above derives exactly those equalities. -/
theorem cyclicFourTwoBasis_complete :
    BasisFor cyclicFourTwo.semigroup cyclicFourTwoBasis := by
  refine ⟨cyclicFourTwoBasis_models, ?_⟩
  intro e valid
  have lengthState :
      cyclicFourTwoState e.lhs.toList.length =
        cyclicFourTwoState e.rhs.toList.length := by
    have evaluated := valid (weightedValuation unitWeight)
    rw [cyclicFourTwoEval_unit, cyclicFourTwoEval_unit] at evaluated
    exact evaluated
  have weightedState :
      ∀ z,
        cyclicFourTwoState
            (e.lhs.toList.length + e.lhs.toList.count z) =
          cyclicFourTwoState
            (e.rhs.toList.length + e.rhs.toList.count z) := by
    intro z
    have evaluated := valid (weightedValuation (doubledWeight z))
    rw [cyclicFourTwoEval_doubled,
      cyclicFourTwoEval_doubled] at evaluated
    exact evaluated
  have complementedState :
      ∀ z,
        cyclicFourTwoState
            (2 * e.lhs.toList.length - e.lhs.toList.count z) =
          cyclicFourTwoState
            (2 * e.rhs.toList.length - e.rhs.toList.count z) := by
    intro z
    have evaluated :=
      valid (weightedValuation (complementedWeight z))
    rw [cyclicFourTwoEval_complemented,
      cyclicFourTwoEval_complemented] at evaluated
    exact evaluated
  have lhsPos : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      apply (cyclicFourTwoState_eq_one rhsPos).mp
      rw [← lengthState, lhsOne]
    have countEq : ∀ z,
        e.lhs.toList.count z = e.rhs.toList.count z := by
      intro z
      apply cyclicFourTwoState_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length (a := z) (l := e.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length (a := z) (l := e.rhs.toList))
      · simpa [lhsOne, rhsOne] using weightedState z
    exact cyclicFourTwoDerivesPermutation e.lhs e.rhs <|
      List.perm_iff_count.mpr countEq
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        apply (cyclicFourTwoState_eq_two rhsPos).mp
        rw [← lengthState, lhsTwo]
      have countEq : ∀ z,
          e.lhs.toList.count z = e.rhs.toList.count z := by
        intro z
        apply cyclicFourTwoState_two_add_injective
        · simpa [lhsTwo] using
            (List.count_le_length (a := z) (l := e.lhs.toList))
        · simpa [rhsTwo] using
            (List.count_le_length (a := z) (l := e.rhs.toList))
        · simpa [lhsTwo, rhsTwo] using weightedState z
      exact cyclicFourTwoDerivesPermutation e.lhs e.rhs <|
        List.perm_iff_count.mpr countEq
    · by_cases lhsThree : e.lhs.toList.length = 3
      · have rhsThree : e.rhs.toList.length = 3 := by
          apply (cyclicFourTwoState_eq_three rhsPos).mp
          rw [← lengthState, lhsThree]
        have countEq : ∀ z,
            e.lhs.toList.count z = e.rhs.toList.count z := by
          intro z
          apply cyclicFourTwoState_three_count_injective
          · simpa [lhsThree] using
              (List.count_le_length (a := z) (l := e.lhs.toList))
          · simpa [rhsThree] using
              (List.count_le_length (a := z) (l := e.rhs.toList))
          · simpa [lhsThree, rhsThree] using weightedState z
          · simpa [lhsThree, rhsThree] using complementedState z
        exact cyclicFourTwoDerivesPermutation e.lhs e.rhs <|
          List.perm_iff_count.mpr countEq
      · have lhsLong : 4 ≤ e.lhs.toList.length := by omega
        have rhsNotOne : e.rhs.toList.length ≠ 1 := by
          intro rhsOne
          have lhsStateOne :
              cyclicFourTwoState e.lhs.toList.length =
                cyclicFourTwoState 1 := by
            rw [lengthState, rhsOne]
          exact lhsOne <|
            (cyclicFourTwoState_eq_one lhsPos).mp lhsStateOne
        have rhsNotTwo : e.rhs.toList.length ≠ 2 := by
          intro rhsTwo
          have lhsStateTwo :
              cyclicFourTwoState e.lhs.toList.length =
                cyclicFourTwoState 2 := by
            rw [lengthState, rhsTwo]
          exact lhsTwo <|
            (cyclicFourTwoState_eq_two lhsPos).mp lhsStateTwo
        have rhsNotThree : e.rhs.toList.length ≠ 3 := by
          intro rhsThree
          have lhsStateThree :
              cyclicFourTwoState e.lhs.toList.length =
                cyclicFourTwoState 3 := by
            rw [lengthState, rhsThree]
          exact lhsThree <|
            (cyclicFourTwoState_eq_three lhsPos).mp lhsStateThree
        have rhsLong : 4 ≤ e.rhs.toList.length := by omega
        have lengthParity :
            e.lhs.toList.length % 2 =
              e.rhs.toList.length % 2 :=
          cyclicFourTwoState_long_parity lhsLong rhsLong lengthState
        have parityEq :
            ∀ z,
              e.lhs.toList.count z % 2 =
                e.rhs.toList.count z % 2 := by
          intro z
          have totalParity :=
            cyclicFourTwoState_long_parity
              (m := e.lhs.toList.length + e.lhs.toList.count z)
              (n := e.rhs.toList.length + e.rhs.toList.count z)
              (by omega) (by omega) (weightedState z)
          rw [Nat.add_mod, Nat.add_mod] at totalParity
          omega
        exact cyclicFourTwoDerivesLongParity
          e.lhs e.rhs lhsLong rhsLong parityEq

theorem cyclicFourTwo_selfDual :
    cyclicFourTwo.semigroup.opposite = cyclicFourTwo.semigroup := by
  unfold cyclicFourTwo FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem cyclicFourTwoOppositeBasis_complete :
    BasisFor cyclicFourTwo.semigroup.opposite cyclicFourTwoBasis := by
  rw [cyclicFourTwo_selfDual]
  exact cyclicFourTwoBasis_complete

end SemigroupBasis.CoRoots.S5_60

import SemigroupBasis.Examples.CyclicTwo
import SemigroupBasis.FiniteTable
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based table of the cyclic semigroup `C_{3,2}`:
`[[1,1,3,3],[1,1,3,3],[3,3,1,1],[3,3,1,2]]`. -/
def cyclicThreeTwoMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else 2
  else if a = 1 then
    if b = 0 then 0 else if b = 1 then 0 else if b = 2 then 2 else 2
  else if a = 2 then
    if b = 0 then 2 else if b = 1 then 2 else if b = 2 then 0 else 0
  else
    if b = 0 then 2 else if b = 1 then 2 else if b = 2 then 0 else 1

/-- The four-element cyclic semigroup with index three and period two. -/
def cyclicThreeTwo : FiniteTable where
  order := 4
  mul := cyclicThreeTwoMul
  assoc := by decide

def cyclicThreeTwoXY : Word Nat := ⟨0, [1]⟩
def cyclicThreeTwoYX : Word Nat := ⟨1, [0]⟩
def cyclicThreeTwoXXYZT : Word Nat := ⟨0, [0, 1, 2, 3]⟩
def cyclicThreeTwoYZT : Word Nat := ⟨1, [2, 3]⟩

def cyclicThreeTwoCommutativityLaw : Identity Nat :=
  ⟨cyclicThreeTwoXY, cyclicThreeTwoYX⟩

def cyclicThreeTwoLongCancellationLaw : Identity Nat :=
  ⟨cyclicThreeTwoXXYZT, cyclicThreeTwoYZT⟩

/-- The basis `xy = yx`, `xxyzt = yzt` for `C_{3,2}`. -/
def cyclicThreeTwoBasis : List (Identity Nat) :=
  [cyclicThreeTwoCommutativityLaw, cyclicThreeTwoLongCancellationLaw]

private def instantiateFourWords
    (u v w t : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | 3 => t
  | n + 4 => Word.singleton (n + 4)

theorem cyclicThreeTwoDerivesCommutativity (u v : Word Nat) :
    Derives cyclicThreeTwoBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicThreeTwoBasis cyclicThreeTwoXY cyclicThreeTwoYX :=
    Derives.fromBasis (e := cyclicThreeTwoCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateFourWords u v v v)
  simpa [cyclicThreeTwoBasis, cyclicThreeTwoCommutativityLaw,
    cyclicThreeTwoXY, cyclicThreeTwoYX, instantiateFourWords, Word.bind,
    Word.append, Word.singleton] using h

theorem cyclicThreeTwoDerivesCancelSquare
    (u v w t : Word Nat) :
    Derives cyclicThreeTwoBasis
      ((((u ++ u) ++ v) ++ w) ++ t) ((v ++ w) ++ t) := by
  have hbase :
      Derives cyclicThreeTwoBasis
        cyclicThreeTwoXXYZT cyclicThreeTwoYZT :=
    Derives.fromBasis (e := cyclicThreeTwoLongCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateFourWords u v w t)
  simpa [cyclicThreeTwoBasis, cyclicThreeTwoLongCancellationLaw,
    cyclicThreeTwoXXYZT, cyclicThreeTwoYZT, instantiateFourWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicThreeTwoBasis
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
              cyclicThreeTwoDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicThreeTwoDerivesCommutativity
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

theorem cyclicThreeTwoDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicThreeTwoBasis u v := by
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
immutable while allowing the `C_{3,2}` argument to replay the derivation. -/
theorem cyclicThreeTwoDerivesCyclicParity (u v : Word Nat)
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

/-- A derivation for `C₂` can be replayed after any fixed product of three
nonempty words. That product supplies the residual `yzt` context required by
`xxyzt = yzt`. -/
theorem cyclicThreeTwoLiftCyclic
    {u v : Word Nat}
    (h : Derives cyclicTwoBasis u v)
    (a b c : Word Nat) (σ : Nat → Word Nat) :
    Derives cyclicThreeTwoBasis
      (((a ++ b) ++ c) ++ u.bind σ)
      (((a ++ b) ++ c) ++ v.bind σ) := by
  induction h generalizing a b c σ with
  | fromBasis hmem =>
      simp only [cyclicTwoBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · have commute :=
          cyclicThreeTwoDerivesCommutativity (σ 0) (σ 1)
        simpa [cyclicCommutativityLaw, cyclicXY, cyclicYX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend ((a ++ b) ++ c) commute
      · let marker := (a ++ b) ++ c
        let square := σ 0 ++ σ 0
        have enter :=
          Derives.appendRight
            (cyclicThreeTwoDerivesCommutativity marker square) (σ 1)
        have cancel :=
          cyclicThreeTwoDerivesCancelSquare (σ 0) a b (c ++ σ 1)
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

private def markerLetter : Word Nat := Word.singleton 0

private def parityMarker : Word Nat :=
  (markerLetter ++ markerLetter) ++ markerLetter

private theorem cyclicThreeTwoDerivesMarkerExpansion
    (w : Word Nat) (long : 3 ≤ w.toList.length) :
    Derives cyclicThreeTwoBasis
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
              have inserted :=
                Derives.symm <|
                  cyclicThreeTwoDerivesCancelSquare parityMarker
                    (Word.singleton head) (Word.singleton next)
                    (wordOfCons third remaining)
              simpa [parityMarker, markerLetter, wordOfCons,
                Word.append, Word.singleton, Word.append_assoc] using inserted

/-- Long words with equal exponent parities are derivably equal. -/
theorem cyclicThreeTwoDerivesLongParity
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (parityEq :
      ∀ z, u.toList.count z % 2 = v.toList.count z % 2) :
    Derives cyclicThreeTwoBasis u v := by
  have expandedU := cyclicThreeTwoDerivesMarkerExpansion u uLong
  have expandedV := cyclicThreeTwoDerivesMarkerExpansion v vLong
  have markedParity :
      ∀ z,
        (parityMarker ++ u).toList.count z % 2 =
          (parityMarker ++ v).toList.count z % 2 := by
    intro z
    simp only [Word.toList_append, List.count_append]
    rw [Nat.add_mod, Nat.add_mod, parityEq z]
    omega
  have cyclic :=
    cyclicThreeTwoDerivesCyclicParity
      (parityMarker ++ u) (parityMarker ++ v)
      markedParity
  have lifted :=
    cyclicThreeTwoLiftCyclic cyclic
      markerLetter markerLetter markerLetter Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact Derives.trans expandedU <|
    Derives.trans
      (by
        simpa [parityMarker, Word.append_assoc] using lifted)
      (Derives.symm expandedV)

/-- The state of the power `aⁿ`, where element `3` is the generator:
`a, a², a³, a⁴, ... = 3,1,2,0,2,0,...`. -/
private def cyclicThreeTwoState (n : Nat) : Fin 4 :=
  if n = 1 then 3
  else if n = 2 then 1
  else if n % 2 = 0 then 0
  else 2

private theorem cyclicThreeTwoMul_state_one
    (n : Nat) (nPos : 0 < n) :
    cyclicThreeTwoMul (cyclicThreeTwoState n)
        (cyclicThreeTwoState 1) =
      cyclicThreeTwoState (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hnEven : n % 2 = 0
      · have hn0 : n ≠ 0 := by omega
        have hnext : (n + 1) % 2 = 1 := by omega
        apply Fin.ext
        simp [cyclicThreeTwoState, cyclicThreeTwoMul,
          hn0, hn1, hn2, hnEven, hnext]
      · have hnOdd : n % 2 = 1 := by omega
        have hn0 : n ≠ 0 := by omega
        have hnext : (n + 1) % 2 = 0 := by omega
        apply Fin.ext
        simp [cyclicThreeTwoState, cyclicThreeTwoMul,
          hn0, hn1, hn2, hnOdd, hnext]

private theorem cyclicThreeTwoMul_state_two
    (n : Nat) (nPos : 0 < n) :
    cyclicThreeTwoMul (cyclicThreeTwoState n)
        (cyclicThreeTwoState 2) =
      cyclicThreeTwoState (n + 2) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · by_cases hnEven : n % 2 = 0
      · have hn0 : n ≠ 0 := by omega
        have hnext : (n + 2) % 2 = 0 := by omega
        apply Fin.ext
        simp [cyclicThreeTwoState, cyclicThreeTwoMul,
          hn0, hn1, hn2, hnEven, hnext]
      · have hnOdd : n % 2 = 1 := by omega
        have hn0 : n ≠ 0 := by omega
        have hnext : (n + 2) % 2 = 1 := by omega
        apply Fin.ext
        simp [cyclicThreeTwoState, cyclicThreeTwoMul,
          hn0, hn1, hn2, hnOdd, hnext]

private def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => weight x + weightSum weight xs

private def weightedValuation (weight : Nat → Nat) : Nat → Fin 4 :=
  fun x => cyclicThreeTwoState (weight x)

private theorem cyclicThreeTwoFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current x =>
          cyclicThreeTwoMul current (weightedValuation weight x))
        (cyclicThreeTwoState acc) =
      cyclicThreeTwoState (acc + weightSum weight xs) := by
  induction xs generalizing acc with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo x with hx | hx
      · rw [show weightedValuation weight x =
            cyclicThreeTwoState 1 by simp [weightedValuation, hx]]
        rw [cyclicThreeTwoMul_state_one acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicThreeTwoMul current (weightedValuation weight x))
              (cyclicThreeTwoState (acc + 1)) =
            cyclicThreeTwoState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 1) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega
      · rw [show weightedValuation weight x =
            cyclicThreeTwoState 2 by simp [weightedValuation, hx]]
        rw [cyclicThreeTwoMul_state_two acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicThreeTwoMul current (weightedValuation weight x))
              (cyclicThreeTwoState (acc + 2)) =
            cyclicThreeTwoState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 2) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega

private theorem cyclicThreeTwoEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (w : Word Nat) :
    cyclicThreeTwo.semigroup.eval (weightedValuation weight) w =
      cyclicThreeTwoState (weightSum weight w.toList) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicThreeTwoMul current (weightedValuation weight x))
            (weightedValuation weight head) =
          cyclicThreeTwoState
            (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          cyclicThreeTwoState (weight head) by rfl]
      have headPos : 0 < weight head := by
        rcases oneOrTwo head with h | h <;> omega
      rw [cyclicThreeTwoFold_weighted weight oneOrTwo tail
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

private theorem cyclicThreeTwoEval_unit (w : Word Nat) :
    cyclicThreeTwo.semigroup.eval (weightedValuation unitWeight) w =
      cyclicThreeTwoState w.toList.length := by
  rw [cyclicThreeTwoEval_weighted unitWeight (by
    intro x
    exact Or.inl rfl)]
  rw [weightSum_unit]

private theorem cyclicThreeTwoEval_doubled (z : Nat) (w : Word Nat) :
    cyclicThreeTwo.semigroup.eval (weightedValuation (doubledWeight z)) w =
      cyclicThreeTwoState (w.toList.length + w.toList.count z) := by
  rw [cyclicThreeTwoEval_weighted (doubledWeight z) (by
    intro x
    by_cases hx : x = z
    · exact Or.inr (by simp [doubledWeight, hx])
    · exact Or.inl (by simp [doubledWeight, hx]))]
  rw [weightSum_doubled]

private theorem cyclicThreeTwoState_eq_one
    {n : Nat} (nPos : 0 < n) :
    cyclicThreeTwoState n = cyclicThreeTwoState 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · exact hn1
    · by_cases hn2 : n = 2
      · subst n
        simp [cyclicThreeTwoState] at h
      · by_cases hnEven : n % 2 = 0
        · simp [cyclicThreeTwoState, hn1, hn2, hnEven] at h
        · simp [cyclicThreeTwoState, hn1, hn2, hnEven] at h
  · intro h
    rw [h]

private theorem cyclicThreeTwoState_eq_two
    {n : Nat} (nPos : 0 < n) :
    cyclicThreeTwoState n = cyclicThreeTwoState 2 ↔ n = 2 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · subst n
      simp [cyclicThreeTwoState] at h
    · by_cases hn2 : n = 2
      · exact hn2
      · by_cases hnEven : n % 2 = 0
        · simp [cyclicThreeTwoState, hn1, hn2, hnEven] at h
        · simp [cyclicThreeTwoState, hn1, hn2, hnEven] at h
  · intro h
    rw [h]

private theorem cyclicThreeTwoState_long_parity
    {m n : Nat} (mLong : 3 ≤ m) (nLong : 3 ≤ n)
    (h : cyclicThreeTwoState m = cyclicThreeTwoState n) :
    m % 2 = n % 2 := by
  have hm1 : m ≠ 1 := by omega
  have hm2 : m ≠ 2 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  by_cases hmEven : m % 2 = 0
  · by_cases hnEven : n % 2 = 0
    · exact hmEven.trans hnEven.symm
    · have hnOdd : n % 2 = 1 := by omega
      simp [cyclicThreeTwoState, hm1, hm2, hn1, hn2,
        hmEven, hnEven] at h
  · have hmOdd : m % 2 = 1 := by omega
    by_cases hnEven : n % 2 = 0
    · simp [cyclicThreeTwoState, hm1, hm2, hn1, hn2,
        hmEven, hnEven] at h
    · have hnOdd : n % 2 = 1 := by omega
      exact hmOdd.trans hnOdd.symm

private theorem cyclicThreeTwoState_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (h :
      cyclicThreeTwoState (1 + m) =
        cyclicThreeTwoState (1 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 := by omega
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hm with rfl | rfl <;>
    rcases hn with rfl | rfl <;>
    simp [cyclicThreeTwoState] at h ⊢

private theorem cyclicThreeTwoState_two_add_injective
    {m n : Nat} (mLe : m ≤ 2) (nLe : n ≤ 2)
    (h :
      cyclicThreeTwoState (2 + m) =
        cyclicThreeTwoState (2 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hm with rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl <;>
    simp [cyclicThreeTwoState] at h ⊢

def cyclicThreeTwoFiniteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def cyclicThreeTwoFiniteLongCancellationLaw : Identity (Fin 4) :=
  ⟨⟨0, [0, 1, 2, 3]⟩, ⟨1, [2, 3]⟩⟩

theorem cyclicThreeTwoFiniteCommutativityLaw_map :
    cyclicThreeTwoFiniteCommutativityLaw.map Fin.val =
      cyclicThreeTwoCommutativityLaw := rfl

theorem cyclicThreeTwoFiniteLongCancellationLaw_map :
    cyclicThreeTwoFiniteLongCancellationLaw.map Fin.val =
      cyclicThreeTwoLongCancellationLaw := rfl

set_option maxRecDepth 100000 in
theorem cyclicThreeTwoBasis_models :
    Models cyclicThreeTwo.semigroup cyclicThreeTwoBasis := by
  intro e he
  simp only [cyclicThreeTwoBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← cyclicThreeTwoFiniteCommutativityLaw_map]
    exact cyclicThreeTwo.checkIdentityNat_sound
      cyclicThreeTwoFiniteCommutativityLaw (by decide)
  · rw [← cyclicThreeTwoFiniteLongCancellationLaw_map]
    exact cyclicThreeTwo.checkIdentityNat_sound
      cyclicThreeTwoFiniteLongCancellationLaw (by decide)

/-- Unrestricted completeness over `Nat` variables. Lengths one and two retain
their exact commutative multisets. At length at least three, weighted
evaluations recover only the exponent-parity vector, and the contextual `C₂`
replay above derives exactly those equalities. -/
theorem cyclicThreeTwoValid_class
    (e : Identity Nat)
    (valid : e.SatisfiedBy cyclicThreeTwo.semigroup) :
    (e.lhs.toList.length = 1 ∧
        e.rhs.toList.length = 1 ∧
        e.lhs.toList.Perm e.rhs.toList) ∨
      (e.lhs.toList.length = 2 ∧
        e.rhs.toList.length = 2 ∧
        e.lhs.toList.Perm e.rhs.toList) ∨
      (3 ≤ e.lhs.toList.length ∧
        3 ≤ e.rhs.toList.length ∧
        ∀ z, e.lhs.toList.count z % 2 =
          e.rhs.toList.count z % 2) := by
  have lengthState :
      cyclicThreeTwoState e.lhs.toList.length =
        cyclicThreeTwoState e.rhs.toList.length := by
    have evaluated := valid (weightedValuation unitWeight)
    rw [cyclicThreeTwoEval_unit, cyclicThreeTwoEval_unit] at evaluated
    exact evaluated
  have weightedState :
      ∀ z,
        cyclicThreeTwoState
            (e.lhs.toList.length + e.lhs.toList.count z) =
          cyclicThreeTwoState
            (e.rhs.toList.length + e.rhs.toList.count z) := by
    intro z
    have evaluated := valid (weightedValuation (doubledWeight z))
    rw [cyclicThreeTwoEval_doubled,
      cyclicThreeTwoEval_doubled] at evaluated
    exact evaluated
  have lhsPos : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      apply (cyclicThreeTwoState_eq_one rhsPos).mp
      rw [← lengthState, lhsOne]
    have countEq : ∀ z,
        e.lhs.toList.count z = e.rhs.toList.count z := by
      intro z
      apply cyclicThreeTwoState_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length (a := z) (l := e.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length (a := z) (l := e.rhs.toList))
      · simpa [lhsOne, rhsOne] using weightedState z
    exact Or.inl ⟨lhsOne, rhsOne, List.perm_iff_count.mpr countEq⟩
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        apply (cyclicThreeTwoState_eq_two rhsPos).mp
        rw [← lengthState, lhsTwo]
      have countEq : ∀ z,
          e.lhs.toList.count z = e.rhs.toList.count z := by
        intro z
        apply cyclicThreeTwoState_two_add_injective
        · simpa [lhsTwo] using
            (List.count_le_length (a := z) (l := e.lhs.toList))
        · simpa [rhsTwo] using
            (List.count_le_length (a := z) (l := e.rhs.toList))
        · simpa [lhsTwo, rhsTwo] using weightedState z
      exact Or.inr <| Or.inl
        ⟨lhsTwo, rhsTwo, List.perm_iff_count.mpr countEq⟩
    · have lhsLong : 3 ≤ e.lhs.toList.length := by omega
      have rhsNotOne : e.rhs.toList.length ≠ 1 := by
        intro rhsOne
        have lhsStateOne :
            cyclicThreeTwoState e.lhs.toList.length =
              cyclicThreeTwoState 1 := by
          rw [lengthState, rhsOne]
        exact lhsOne <|
          (cyclicThreeTwoState_eq_one lhsPos).mp lhsStateOne
      have rhsNotTwo : e.rhs.toList.length ≠ 2 := by
        intro rhsTwo
        have lhsStateTwo :
            cyclicThreeTwoState e.lhs.toList.length =
              cyclicThreeTwoState 2 := by
          rw [lengthState, rhsTwo]
        exact lhsTwo <|
          (cyclicThreeTwoState_eq_two lhsPos).mp lhsStateTwo
      have rhsLong : 3 ≤ e.rhs.toList.length := by omega
      have lengthParity :
          e.lhs.toList.length % 2 =
            e.rhs.toList.length % 2 :=
        cyclicThreeTwoState_long_parity lhsLong rhsLong lengthState
      have parityEq :
          ∀ z,
            e.lhs.toList.count z % 2 =
              e.rhs.toList.count z % 2 := by
        intro z
        have totalParity :=
          cyclicThreeTwoState_long_parity
            (m := e.lhs.toList.length + e.lhs.toList.count z)
            (n := e.rhs.toList.length + e.rhs.toList.count z)
            (by omega) (by omega) (weightedState z)
        rw [Nat.add_mod, Nat.add_mod] at totalParity
        omega
      exact Or.inr <| Or.inr ⟨lhsLong, rhsLong, parityEq⟩

theorem cyclicThreeTwoBasis_complete :
    BasisFor cyclicThreeTwo.semigroup cyclicThreeTwoBasis := by
  refine ⟨cyclicThreeTwoBasis_models, ?_⟩
  intro e valid
  have lengthState :
      cyclicThreeTwoState e.lhs.toList.length =
        cyclicThreeTwoState e.rhs.toList.length := by
    have evaluated := valid (weightedValuation unitWeight)
    rw [cyclicThreeTwoEval_unit, cyclicThreeTwoEval_unit] at evaluated
    exact evaluated
  have weightedState :
      ∀ z,
        cyclicThreeTwoState
            (e.lhs.toList.length + e.lhs.toList.count z) =
          cyclicThreeTwoState
            (e.rhs.toList.length + e.rhs.toList.count z) := by
    intro z
    have evaluated := valid (weightedValuation (doubledWeight z))
    rw [cyclicThreeTwoEval_doubled,
      cyclicThreeTwoEval_doubled] at evaluated
    exact evaluated
  have lhsPos : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      apply (cyclicThreeTwoState_eq_one rhsPos).mp
      rw [← lengthState, lhsOne]
    have countEq : ∀ z,
        e.lhs.toList.count z = e.rhs.toList.count z := by
      intro z
      apply cyclicThreeTwoState_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length (a := z) (l := e.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length (a := z) (l := e.rhs.toList))
      · simpa [lhsOne, rhsOne] using weightedState z
    exact cyclicThreeTwoDerivesPermutation e.lhs e.rhs <|
      List.perm_iff_count.mpr countEq
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        apply (cyclicThreeTwoState_eq_two rhsPos).mp
        rw [← lengthState, lhsTwo]
      have countEq : ∀ z,
          e.lhs.toList.count z = e.rhs.toList.count z := by
        intro z
        apply cyclicThreeTwoState_two_add_injective
        · simpa [lhsTwo] using
            (List.count_le_length (a := z) (l := e.lhs.toList))
        · simpa [rhsTwo] using
            (List.count_le_length (a := z) (l := e.rhs.toList))
        · simpa [lhsTwo, rhsTwo] using weightedState z
      exact cyclicThreeTwoDerivesPermutation e.lhs e.rhs <|
        List.perm_iff_count.mpr countEq
    · have lhsLong : 3 ≤ e.lhs.toList.length := by omega
      have rhsNotOne : e.rhs.toList.length ≠ 1 := by
        intro rhsOne
        have lhsStateOne :
            cyclicThreeTwoState e.lhs.toList.length =
              cyclicThreeTwoState 1 := by
          rw [lengthState, rhsOne]
        exact lhsOne <|
          (cyclicThreeTwoState_eq_one lhsPos).mp lhsStateOne
      have rhsNotTwo : e.rhs.toList.length ≠ 2 := by
        intro rhsTwo
        have lhsStateTwo :
            cyclicThreeTwoState e.lhs.toList.length =
              cyclicThreeTwoState 2 := by
          rw [lengthState, rhsTwo]
        exact lhsTwo <|
          (cyclicThreeTwoState_eq_two lhsPos).mp lhsStateTwo
      have rhsLong : 3 ≤ e.rhs.toList.length := by omega
      have lengthParity :
          e.lhs.toList.length % 2 =
            e.rhs.toList.length % 2 :=
        cyclicThreeTwoState_long_parity lhsLong rhsLong lengthState
      have parityEq :
          ∀ z,
            e.lhs.toList.count z % 2 =
              e.rhs.toList.count z % 2 := by
        intro z
        have totalParity :=
          cyclicThreeTwoState_long_parity
            (m := e.lhs.toList.length + e.lhs.toList.count z)
            (n := e.rhs.toList.length + e.rhs.toList.count z)
            (by omega) (by omega) (weightedState z)
        rw [Nat.add_mod, Nat.add_mod] at totalParity
        omega
      exact cyclicThreeTwoDerivesLongParity
        e.lhs e.rhs lhsLong rhsLong parityEq

theorem cyclicThreeTwoOppositeBasis_complete :
    BasisFor cyclicThreeTwo.semigroup.opposite
      (reversedBasis cyclicThreeTwoBasis) :=
  cyclicThreeTwoBasis_complete.oppositeReversed

end SemigroupBasis.Examples

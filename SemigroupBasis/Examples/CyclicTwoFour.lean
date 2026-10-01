import SemigroupBasis.Examples.CyclicFour
import SemigroupBasis.FiniteTable
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based table of the cyclic semigroup `C_{2,4}`:
`[[1,2,3,3,5],[2,1,5,5,3],[3,5,2,2,1],[3,5,2,2,1],
[5,3,1,1,2]]`. -/
def cyclicTwoFourMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    if b = 0 then 0
    else if b = 1 then 1
    else if b = 2 then 2
    else if b = 3 then 2
    else 4
  else if a = 1 then
    if b = 0 then 1
    else if b = 1 then 0
    else if b = 2 then 4
    else if b = 3 then 4
    else 2
  else if a = 2 then
    if b = 0 then 2
    else if b = 1 then 4
    else if b = 2 then 1
    else if b = 3 then 1
    else 0
  else if a = 3 then
    if b = 0 then 2
    else if b = 1 then 4
    else if b = 2 then 1
    else if b = 3 then 1
    else 0
  else
    if b = 0 then 4
    else if b = 1 then 2
    else if b = 2 then 0
    else if b = 3 then 0
    else 1

/-- The five-element cyclic semigroup with index two and period four. -/
def cyclicTwoFour : FiniteTable where
  order := 5
  mul := cyclicTwoFourMul
  assoc := by decide

def cyclicTwoFourXY : Word Nat := ⟨0, [1]⟩
def cyclicTwoFourYX : Word Nat := ⟨1, [0]⟩
def cyclicTwoFourXXXXYZ : Word Nat := ⟨0, [0, 0, 0, 1, 2]⟩
def cyclicTwoFourYZ : Word Nat := ⟨1, [2]⟩

def cyclicTwoFourCommutativityLaw : Identity Nat :=
  ⟨cyclicTwoFourXY, cyclicTwoFourYX⟩

def cyclicTwoFourLongCancellationLaw : Identity Nat :=
  ⟨cyclicTwoFourXXXXYZ, cyclicTwoFourYZ⟩

/-- The basis `xy = yx`, `xxxxyz = yz` for `C_{2,4}`. -/
def cyclicTwoFourBasis : List (Identity Nat) :=
  [cyclicTwoFourCommutativityLaw, cyclicTwoFourLongCancellationLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem cyclicTwoFourDerivesCommutativity (u v : Word Nat) :
    Derives cyclicTwoFourBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicTwoFourBasis cyclicTwoFourXY cyclicTwoFourYX :=
    Derives.fromBasis (e := cyclicTwoFourCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [cyclicTwoFourBasis, cyclicTwoFourCommutativityLaw,
    cyclicTwoFourXY, cyclicTwoFourYX, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton] using h

theorem cyclicTwoFourDerivesCancelFourth
    (u v w : Word Nat) :
    Derives cyclicTwoFourBasis
      (((((u ++ u) ++ u) ++ u) ++ v) ++ w) (v ++ w) := by
  have hbase :
      Derives cyclicTwoFourBasis
        cyclicTwoFourXXXXYZ cyclicTwoFourYZ :=
    Derives.fromBasis (e := cyclicTwoFourLongCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [cyclicTwoFourBasis, cyclicTwoFourLongCancellationLaw,
    cyclicTwoFourXXXXYZ, cyclicTwoFourYZ, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicTwoFourBasis
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
              cyclicTwoFourDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicTwoFourDerivesCommutativity
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

theorem cyclicTwoFourDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicTwoFourBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Equal exponent vectors modulo four are exactly the derivable identities
of the cyclic group of order four. This local wrapper exposes the syntactic
part of `cyclicFourBasis_complete` for contextual replay. -/
theorem cyclicTwoFourDerivesCyclicModFour
    (u v : Word Nat)
    (modEq :
      ∀ z, u.toList.count z % 4 = v.toList.count z % 4) :
    Derives cyclicFourBasis u v := by
  have reducedPerm :
      (quaternaryReduce u.toList).Perm (quaternaryReduce v.toList) :=
    quaternaryReduce_perm_of_mod_eq modEq
  have lhsNormal := cyclicFourDerivesNormal u
  have rhsNormal := cyclicFourDerivesNormal v
  cases hl : quaternaryReduce u.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : quaternaryReduce v.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicFourDerivesCommonFourth
            (Word.singleton u.head) (Word.singleton v.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : quaternaryReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (cyclicFourDerivesPermutation
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

/-- A cyclic-group derivation can be replayed after any fixed product of two
nonempty words. That product supplies the residual `yz` context required by
`xxxxyz = yz`. -/
theorem cyclicTwoFourLiftCyclic
    {u v : Word Nat}
    (h : Derives cyclicFourBasis u v)
    (a b : Word Nat) (σ : Nat → Word Nat) :
    Derives cyclicTwoFourBasis
      ((a ++ b) ++ u.bind σ)
      ((a ++ b) ++ v.bind σ) := by
  induction h generalizing a b σ with
  | fromBasis hmem =>
      simp only [cyclicFourBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · have commute :=
          cyclicTwoFourDerivesCommutativity (σ 0) (σ 1)
        simpa [cyclicFourCommutativityLaw, cyclicFourXY,
          cyclicFourYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend (a ++ b) commute
      · let marker := a ++ b
        let fourth := ((σ 0 ++ σ 0) ++ σ 0) ++ σ 0
        have enter :=
          Derives.appendRight
            (cyclicTwoFourDerivesCommutativity marker fourth) (σ 1)
        have cancel :=
          cyclicTwoFourDerivesCancelFourth (σ 0) a (b ++ σ 1)
        exact Derives.trans
          (by
            simpa [cyclicFourCancellationLaw, cyclicFourXXXXY,
              cyclicFourY, marker, fourth, Word.bind, Word.append,
              Word.singleton, Word.append_assoc] using enter)
          (by
            simpa [cyclicFourCancellationLaw, cyclicFourXXXXY,
              cyclicFourY, marker, Word.bind, Word.append,
              Word.singleton, Word.append_assoc] using cancel)
  | refl =>
      exact Derives.refl _
  | symm _ ih =>
      exact Derives.symm (ih a b σ)
  | trans _ _ ih₁ ih₂ =>
      exact Derives.trans (ih₁ a b σ) (ih₂ a b σ)
  | prepend p _ ih =>
      simpa [bind_append, Word.append_assoc] using
        ih a (b ++ p.bind σ) σ
  | appendRight _ q ih =>
      simpa [bind_append, Word.append_assoc] using
        Derives.appendRight (ih a b σ) (q.bind σ)
  | subst _ τ ih =>
      simpa [bind_bind] using
        ih a b (fun x => (τ x).bind σ)

private def markerLetter : Word Nat := Word.singleton 0

private theorem cyclicTwoFourDerivesMarkerExpansion
    (w : Word Nat) (long : 2 ≤ w.toList.length) :
    Derives cyclicTwoFourBasis
      w (((markerLetter ++ markerLetter) ++ markerLetter) ++
        (markerLetter ++ w)) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons next rest =>
          have inserted :=
            Derives.symm <|
              cyclicTwoFourDerivesCancelFourth markerLetter
                (Word.singleton head) (wordOfCons next rest)
          simpa [markerLetter, wordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using inserted

/-- Words of length at least two with equal exponent vectors modulo four are
derivably equal from `xy = yx` and `xxxxyz = yz`. -/
theorem cyclicTwoFourDerivesLongModFour
    (u v : Word Nat)
    (uLong : 2 ≤ u.toList.length)
    (vLong : 2 ≤ v.toList.length)
    (modEq :
      ∀ z, u.toList.count z % 4 = v.toList.count z % 4) :
    Derives cyclicTwoFourBasis u v := by
  have expandedU := cyclicTwoFourDerivesMarkerExpansion u uLong
  have expandedV := cyclicTwoFourDerivesMarkerExpansion v vLong
  have markedMod :
      ∀ z,
        (markerLetter ++ u).toList.count z % 4 =
          (markerLetter ++ v).toList.count z % 4 := by
    intro z
    simp only [Word.toList_append, List.count_append]
    rw [Nat.add_mod, Nat.add_mod, modEq z]
    omega
  have cyclic :=
    cyclicTwoFourDerivesCyclicModFour
      (markerLetter ++ u) (markerLetter ++ v) markedMod
  have lifted :=
    cyclicTwoFourLiftCyclic cyclic
      markerLetter (markerLetter ++ markerLetter) Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact Derives.trans expandedU <|
    Derives.trans
      (by simpa [markerLetter, Word.append_assoc] using lifted)
      (Derives.symm expandedV)

/-- The state of the power `aⁿ`, where element `4` in the one-based table is
the generator: `a, a², a³, a⁴, ... = 4,2,5,1,3,2,5,1,...`. -/
private def cyclicTwoFourState (n : Nat) : Fin 5 :=
  if n = 1 then 3
  else if n % 4 = 0 then 0
  else if n % 4 = 1 then 2
  else if n % 4 = 2 then 1
  else 4

private theorem cyclicTwoFourMul_state_one
    (n : Nat) (nPos : 0 < n) :
    cyclicTwoFourMul (cyclicTwoFourState n)
        (cyclicTwoFourState 1) =
      cyclicTwoFourState (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · have hn0 : n ≠ 0 := by omega
    by_cases h0 : n % 4 = 0
    · have hnext : (n + 1) % 4 = 1 := by omega
      apply Fin.ext
      simp [cyclicTwoFourState, cyclicTwoFourMul, hn1,
        hn0, h0, hnext]
    · by_cases h1 : n % 4 = 1
      · have hnext : (n + 1) % 4 = 2 := by omega
        apply Fin.ext
        simp [cyclicTwoFourState, cyclicTwoFourMul, hn1,
          hn0, h1, hnext]
      · by_cases h2 : n % 4 = 2
        · have hnext : (n + 1) % 4 = 3 := by omega
          apply Fin.ext
          simp [cyclicTwoFourState, cyclicTwoFourMul, hn1,
            hn0, h2, hnext]
        · have h3 : n % 4 = 3 := by omega
          have hnext : (n + 1) % 4 = 0 := by omega
          apply Fin.ext
          simp [cyclicTwoFourState, cyclicTwoFourMul, hn1,
            hn0, h3, hnext]

private theorem cyclicTwoFourMul_state_two
    (n : Nat) (nPos : 0 < n) :
    cyclicTwoFourMul (cyclicTwoFourState n)
        (cyclicTwoFourState 2) =
      cyclicTwoFourState (n + 2) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · have hnext1 : n + 2 ≠ 1 := by omega
    by_cases h0 : n % 4 = 0
    · have hnext : (n + 2) % 4 = 2 := by omega
      apply Fin.ext
      simp [cyclicTwoFourState, cyclicTwoFourMul, hn1,
        hnext1, h0, hnext]
    · by_cases h1 : n % 4 = 1
      · have hnext : (n + 2) % 4 = 3 := by omega
        apply Fin.ext
        simp [cyclicTwoFourState, cyclicTwoFourMul, hn1,
          hnext1, h1, hnext]
      · by_cases h2 : n % 4 = 2
        · have hnext : (n + 2) % 4 = 0 := by omega
          apply Fin.ext
          simp [cyclicTwoFourState, cyclicTwoFourMul, hn1,
            hnext1, h2, hnext]
        · have h3 : n % 4 = 3 := by omega
          have hnext : (n + 2) % 4 = 1 := by omega
          apply Fin.ext
          simp [cyclicTwoFourState, cyclicTwoFourMul, hn1,
            hnext1, h3, hnext]

private def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => weight x + weightSum weight xs

private def weightedValuation (weight : Nat → Nat) : Nat → Fin 5 :=
  fun x => cyclicTwoFourState (weight x)

private theorem cyclicTwoFourFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current x =>
          cyclicTwoFourMul current (weightedValuation weight x))
        (cyclicTwoFourState acc) =
      cyclicTwoFourState (acc + weightSum weight xs) := by
  induction xs generalizing acc with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo x with hx | hx
      · rw [show weightedValuation weight x =
            cyclicTwoFourState 1 by simp [weightedValuation, hx]]
        rw [cyclicTwoFourMul_state_one acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicTwoFourMul current
                  (weightedValuation weight x))
              (cyclicTwoFourState (acc + 1)) =
            cyclicTwoFourState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 1) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega
      · rw [show weightedValuation weight x =
            cyclicTwoFourState 2 by simp [weightedValuation, hx]]
        rw [cyclicTwoFourMul_state_two acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicTwoFourMul current
                  (weightedValuation weight x))
              (cyclicTwoFourState (acc + 2)) =
            cyclicTwoFourState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 2) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega

private theorem cyclicTwoFourEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (w : Word Nat) :
    cyclicTwoFour.semigroup.eval (weightedValuation weight) w =
      cyclicTwoFourState (weightSum weight w.toList) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicTwoFourMul current (weightedValuation weight x))
            (weightedValuation weight head) =
          cyclicTwoFourState
            (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          cyclicTwoFourState (weight head) by rfl]
      have headPos : 0 < weight head := by
        rcases oneOrTwo head with h | h <;> omega
      rw [cyclicTwoFourFold_weighted weight oneOrTwo tail
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

private theorem cyclicTwoFourEval_unit (w : Word Nat) :
    cyclicTwoFour.semigroup.eval (weightedValuation unitWeight) w =
      cyclicTwoFourState w.toList.length := by
  rw [cyclicTwoFourEval_weighted unitWeight (by
    intro x
    exact Or.inl rfl)]
  rw [weightSum_unit]

private theorem cyclicTwoFourEval_doubled (z : Nat) (w : Word Nat) :
    cyclicTwoFour.semigroup.eval
        (weightedValuation (doubledWeight z)) w =
      cyclicTwoFourState (w.toList.length + w.toList.count z) := by
  rw [cyclicTwoFourEval_weighted (doubledWeight z) (by
    intro x
    by_cases hx : x = z
    · exact Or.inr (by simp [doubledWeight, hx])
    · exact Or.inl (by simp [doubledWeight, hx]))]
  rw [weightSum_doubled]

private theorem cyclicTwoFourState_eq_one {n : Nat} :
    cyclicTwoFourState n = cyclicTwoFourState 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · exact hn1
    · by_cases h0 : n % 4 = 0
      · simp [cyclicTwoFourState, hn1, h0] at h
      · by_cases h1 : n % 4 = 1
        · simp [cyclicTwoFourState, hn1, h1] at h
        · by_cases h2 : n % 4 = 2
          · simp [cyclicTwoFourState, hn1, h2] at h
          · have h3 : n % 4 = 3 := by omega
            simp [cyclicTwoFourState, hn1, h3] at h
  · intro h
    rw [h]

private theorem cyclicTwoFourState_long_mod_four
    {m n : Nat} (mLong : 2 ≤ m) (nLong : 2 ≤ n)
    (h : cyclicTwoFourState m = cyclicTwoFourState n) :
    m % 4 = n % 4 := by
  have hm1 : m ≠ 1 := by omega
  have hn1 : n ≠ 1 := by omega
  have hm :
      m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
    omega
  have hn :
      n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    omega
  rcases hm with hm | hm | hm | hm <;>
    rcases hn with hn | hn | hn | hn <;>
    simp [cyclicTwoFourState, hm1, hn1, hm, hn] at h ⊢

private theorem cyclicTwoFourState_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (h :
      cyclicTwoFourState (1 + m) =
        cyclicTwoFourState (1 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 := by omega
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hm with rfl | rfl <;>
    rcases hn with rfl | rfl <;>
    simp [cyclicTwoFourState] at h ⊢

def cyclicTwoFourFiniteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def cyclicTwoFourFiniteLongCancellationLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 0, 0, 1, 2]⟩, ⟨1, [2]⟩⟩

theorem cyclicTwoFourFiniteCommutativityLaw_map :
    cyclicTwoFourFiniteCommutativityLaw.map Fin.val =
      cyclicTwoFourCommutativityLaw := rfl

theorem cyclicTwoFourFiniteLongCancellationLaw_map :
    cyclicTwoFourFiniteLongCancellationLaw.map Fin.val =
      cyclicTwoFourLongCancellationLaw := rfl

set_option maxRecDepth 100000 in
theorem cyclicTwoFourBasis_models :
    Models cyclicTwoFour.semigroup cyclicTwoFourBasis := by
  intro e he
  simp only [cyclicTwoFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← cyclicTwoFourFiniteCommutativityLaw_map]
    exact cyclicTwoFour.checkIdentityNat_sound
      cyclicTwoFourFiniteCommutativityLaw (by decide)
  · rw [← cyclicTwoFourFiniteLongCancellationLaw_map]
    exact cyclicTwoFour.checkIdentityNat_sound
      cyclicTwoFourFiniteLongCancellationLaw (by decide)

/-- Unrestricted completeness over `Nat` variables. One-letter words retain
their exact variable. At length at least two, weighted evaluations recover the
exponent vector modulo four, and the contextual cyclic-group replay derives
exactly those equalities. -/
theorem cyclicTwoFourBasis_complete :
    BasisFor cyclicTwoFour.semigroup cyclicTwoFourBasis := by
  refine ⟨cyclicTwoFourBasis_models, ?_⟩
  intro e valid
  have lengthState :
      cyclicTwoFourState e.lhs.toList.length =
        cyclicTwoFourState e.rhs.toList.length := by
    have evaluated := valid (weightedValuation unitWeight)
    rw [cyclicTwoFourEval_unit, cyclicTwoFourEval_unit] at evaluated
    exact evaluated
  have weightedState :
      ∀ z,
        cyclicTwoFourState
            (e.lhs.toList.length + e.lhs.toList.count z) =
          cyclicTwoFourState
            (e.rhs.toList.length + e.rhs.toList.count z) := by
    intro z
    have evaluated := valid (weightedValuation (doubledWeight z))
    rw [cyclicTwoFourEval_doubled,
      cyclicTwoFourEval_doubled] at evaluated
    exact evaluated
  have lhsPos : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      apply cyclicTwoFourState_eq_one.mp
      rw [← lengthState, lhsOne]
    have countEq : ∀ z,
        e.lhs.toList.count z = e.rhs.toList.count z := by
      intro z
      apply cyclicTwoFourState_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length (a := z) (l := e.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length (a := z) (l := e.rhs.toList))
      · simpa [lhsOne, rhsOne] using weightedState z
    exact cyclicTwoFourDerivesPermutation e.lhs e.rhs <|
      List.perm_iff_count.mpr countEq
  · have lhsLong : 2 ≤ e.lhs.toList.length := by omega
    have rhsNotOne : e.rhs.toList.length ≠ 1 := by
      intro rhsOne
      have lhsStateOne :
          cyclicTwoFourState e.lhs.toList.length =
            cyclicTwoFourState 1 := by
        rw [lengthState, rhsOne]
      exact lhsOne <|
        cyclicTwoFourState_eq_one.mp lhsStateOne
    have rhsLong : 2 ≤ e.rhs.toList.length := by omega
    have lengthMod :
        e.lhs.toList.length % 4 =
          e.rhs.toList.length % 4 :=
      cyclicTwoFourState_long_mod_four lhsLong rhsLong lengthState
    have modEq :
        ∀ z,
          e.lhs.toList.count z % 4 =
            e.rhs.toList.count z % 4 := by
      intro z
      have totalMod :=
        cyclicTwoFourState_long_mod_four
          (m := e.lhs.toList.length + e.lhs.toList.count z)
          (n := e.rhs.toList.length + e.rhs.toList.count z)
          (by omega) (by omega) (weightedState z)
      rw [Nat.add_mod, Nat.add_mod] at totalMod
      omega
    exact cyclicTwoFourDerivesLongModFour
      e.lhs e.rhs lhsLong rhsLong modEq

theorem cyclicTwoFour_selfDual :
    cyclicTwoFour.semigroup.opposite = cyclicTwoFour.semigroup := by
  unfold cyclicTwoFour FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem cyclicTwoFourOppositeBasis_complete :
    BasisFor cyclicTwoFour.semigroup.opposite cyclicTwoFourBasis := by
  rw [cyclicTwoFour_selfDual]
  exact cyclicTwoFourBasis_complete

end SemigroupBasis.Examples

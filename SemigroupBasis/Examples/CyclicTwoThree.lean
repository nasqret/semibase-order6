import SemigroupBasis.Examples.CyclicThree
import SemigroupBasis.FiniteTable
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based table of the cyclic semigroup `C_{2,3}`:
`[[1,2,3,3],[2,3,1,1],[3,1,2,2],[3,1,2,2]]`. -/
def cyclicTwoThreeMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then
    if b = 0 then 0 else if b = 1 then 1 else if b = 2 then 2 else 2
  else if a = 1 then
    if b = 0 then 1 else if b = 1 then 2 else if b = 2 then 0 else 0
  else if a = 2 then
    if b = 0 then 2 else if b = 1 then 0 else if b = 2 then 1 else 1
  else
    if b = 0 then 2 else if b = 1 then 0 else if b = 2 then 1 else 1

/-- The four-element cyclic semigroup with index two and period three. -/
def cyclicTwoThree : FiniteTable where
  order := 4
  mul := cyclicTwoThreeMul
  assoc := by decide

def cyclicTwoThreeXY : Word Nat := ⟨0, [1]⟩
def cyclicTwoThreeYX : Word Nat := ⟨1, [0]⟩
def cyclicTwoThreeXXXYZ : Word Nat := ⟨0, [0, 0, 1, 2]⟩
def cyclicTwoThreeYZ : Word Nat := ⟨1, [2]⟩

def cyclicTwoThreeCommutativityLaw : Identity Nat :=
  ⟨cyclicTwoThreeXY, cyclicTwoThreeYX⟩

def cyclicTwoThreeLongCancellationLaw : Identity Nat :=
  ⟨cyclicTwoThreeXXXYZ, cyclicTwoThreeYZ⟩

/-- The basis `xy = yx`, `xxxyz = yz` for `C_{2,3}`. -/
def cyclicTwoThreeBasis : List (Identity Nat) :=
  [cyclicTwoThreeCommutativityLaw, cyclicTwoThreeLongCancellationLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem cyclicTwoThreeDerivesCommutativity (u v : Word Nat) :
    Derives cyclicTwoThreeBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicTwoThreeBasis cyclicTwoThreeXY cyclicTwoThreeYX :=
    Derives.fromBasis (e := cyclicTwoThreeCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [cyclicTwoThreeBasis, cyclicTwoThreeCommutativityLaw,
    cyclicTwoThreeXY, cyclicTwoThreeYX, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton] using h

theorem cyclicTwoThreeDerivesCancelCube
    (u v w : Word Nat) :
    Derives cyclicTwoThreeBasis
      ((((u ++ u) ++ u) ++ v) ++ w) (v ++ w) := by
  have hbase :
      Derives cyclicTwoThreeBasis
        cyclicTwoThreeXXXYZ cyclicTwoThreeYZ :=
    Derives.fromBasis (e := cyclicTwoThreeLongCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [cyclicTwoThreeBasis, cyclicTwoThreeLongCancellationLaw,
    cyclicTwoThreeXXXYZ, cyclicTwoThreeYZ, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicTwoThreeBasis
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
              cyclicTwoThreeDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicTwoThreeDerivesCommutativity
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

theorem cyclicTwoThreeDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicTwoThreeBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Equal exponent vectors modulo three are exactly the derivable identities
of the cyclic group of order three. This local wrapper exposes the syntactic
part of `cyclicThreeBasis_complete` for contextual replay. -/
theorem cyclicTwoThreeDerivesCyclicModThree
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

/-- A cyclic-group derivation can be replayed after any fixed product of two
nonempty words. That product supplies the residual `yz` context required by
`xxxyz = yz`. -/
theorem cyclicTwoThreeLiftCyclic
    {u v : Word Nat}
    (h : Derives cyclicThreeBasis u v)
    (a b : Word Nat) (σ : Nat → Word Nat) :
    Derives cyclicTwoThreeBasis
      ((a ++ b) ++ u.bind σ)
      ((a ++ b) ++ v.bind σ) := by
  induction h generalizing a b σ with
  | fromBasis hmem =>
      simp only [cyclicThreeBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · have commute :=
          cyclicTwoThreeDerivesCommutativity (σ 0) (σ 1)
        simpa [cyclicThreeCommutativityLaw, cyclicThreeXY,
          cyclicThreeYX, Word.bind, Word.append, Word.singleton,
          Word.append_assoc] using
          Derives.prepend (a ++ b) commute
      · let marker := a ++ b
        let cube := (σ 0 ++ σ 0) ++ σ 0
        have enter :=
          Derives.appendRight
            (cyclicTwoThreeDerivesCommutativity marker cube) (σ 1)
        have cancel :=
          cyclicTwoThreeDerivesCancelCube (σ 0) a (b ++ σ 1)
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

private theorem cyclicTwoThreeDerivesMarkerExpansion
    (w : Word Nat) (long : 2 ≤ w.toList.length) :
    Derives cyclicTwoThreeBasis
      w ((markerLetter ++ markerLetter) ++ (markerLetter ++ w)) := by
  cases w with
  | mk head tail =>
      cases tail with
      | nil =>
          simp [Word.toList] at long
      | cons next rest =>
          have inserted :=
            Derives.symm <|
              cyclicTwoThreeDerivesCancelCube markerLetter
                (Word.singleton head) (wordOfCons next rest)
          simpa [markerLetter, wordOfCons, Word.append,
            Word.singleton, Word.append_assoc] using inserted

/-- Words of length at least two with equal exponent vectors modulo three are
derivably equal from `xy = yx` and `xxxyz = yz`. -/
theorem cyclicTwoThreeDerivesLongModThree
    (u v : Word Nat)
    (uLong : 2 ≤ u.toList.length)
    (vLong : 2 ≤ v.toList.length)
    (modEq :
      ∀ z, u.toList.count z % 3 = v.toList.count z % 3) :
    Derives cyclicTwoThreeBasis u v := by
  have expandedU := cyclicTwoThreeDerivesMarkerExpansion u uLong
  have expandedV := cyclicTwoThreeDerivesMarkerExpansion v vLong
  have markedMod :
      ∀ z,
        (markerLetter ++ u).toList.count z % 3 =
          (markerLetter ++ v).toList.count z % 3 := by
    intro z
    simp only [Word.toList_append, List.count_append]
    rw [Nat.add_mod, Nat.add_mod, modEq z]
    omega
  have cyclic :=
    cyclicTwoThreeDerivesCyclicModThree
      (markerLetter ++ u) (markerLetter ++ v) markedMod
  have lifted :=
    cyclicTwoThreeLiftCyclic cyclic
      markerLetter markerLetter Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  exact Derives.trans expandedU <|
    Derives.trans
      (by simpa [markerLetter, Word.append_assoc] using lifted)
      (Derives.symm expandedV)

/-- The state of the power `aⁿ`, where element `4` in the one-based table is
the generator: `a, a², a³, a⁴, ... = 4,2,1,3,2,1,3,...`. -/
private def cyclicTwoThreeState (n : Nat) : Fin 4 :=
  if n = 1 then 3
  else if n % 3 = 0 then 0
  else if n % 3 = 1 then 2
  else 1

private theorem cyclicTwoThreeMul_state_one
    (n : Nat) (nPos : 0 < n) :
    cyclicTwoThreeMul (cyclicTwoThreeState n)
        (cyclicTwoThreeState 1) =
      cyclicTwoThreeState (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · have hn0 : n ≠ 0 := by omega
    by_cases h0 : n % 3 = 0
    · have hnext : (n + 1) % 3 = 1 := by omega
      apply Fin.ext
      simp [cyclicTwoThreeState, cyclicTwoThreeMul, hn1,
        hn0, h0, hnext]
    · by_cases h1 : n % 3 = 1
      · have hnext : (n + 1) % 3 = 2 := by omega
        apply Fin.ext
        simp [cyclicTwoThreeState, cyclicTwoThreeMul, hn1,
          hn0, h1, hnext]
      · have h2 : n % 3 = 2 := by omega
        have hnext : (n + 1) % 3 = 0 := by omega
        apply Fin.ext
        simp [cyclicTwoThreeState, cyclicTwoThreeMul, hn1,
          hn0, h2, hnext]

private theorem cyclicTwoThreeMul_state_two
    (n : Nat) (nPos : 0 < n) :
    cyclicTwoThreeMul (cyclicTwoThreeState n)
        (cyclicTwoThreeState 2) =
      cyclicTwoThreeState (n + 2) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · have hnext1 : n + 2 ≠ 1 := by omega
    by_cases h0 : n % 3 = 0
    · have hnext : (n + 2) % 3 = 2 := by omega
      apply Fin.ext
      simp [cyclicTwoThreeState, cyclicTwoThreeMul, hn1,
        hnext1, h0, hnext]
    · by_cases h1 : n % 3 = 1
      · have hnext : (n + 2) % 3 = 0 := by omega
        apply Fin.ext
        simp [cyclicTwoThreeState, cyclicTwoThreeMul, hn1,
          hnext1, h1, hnext]
      · have h2 : n % 3 = 2 := by omega
        have hnext : (n + 2) % 3 = 1 := by omega
        apply Fin.ext
        simp [cyclicTwoThreeState, cyclicTwoThreeMul, hn1,
          hnext1, h2, hnext]

private def weightSum (weight : Nat → Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => weight x + weightSum weight xs

private def weightedValuation (weight : Nat → Nat) : Nat → Fin 4 :=
  fun x => cyclicTwoThreeState (weight x)

private theorem cyclicTwoThreeFold_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current x =>
          cyclicTwoThreeMul current (weightedValuation weight x))
        (cyclicTwoThreeState acc) =
      cyclicTwoThreeState (acc + weightSum weight xs) := by
  induction xs generalizing acc with
  | nil =>
      simp [weightSum]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases oneOrTwo x with hx | hx
      · rw [show weightedValuation weight x =
            cyclicTwoThreeState 1 by simp [weightedValuation, hx]]
        rw [cyclicTwoThreeMul_state_one acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicTwoThreeMul current
                  (weightedValuation weight x))
              (cyclicTwoThreeState (acc + 1)) =
            cyclicTwoThreeState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 1) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega
      · rw [show weightedValuation weight x =
            cyclicTwoThreeState 2 by simp [weightedValuation, hx]]
        rw [cyclicTwoThreeMul_state_two acc accPos]
        change
          xs.foldl
              (fun current x =>
                cyclicTwoThreeMul current
                  (weightedValuation weight x))
              (cyclicTwoThreeState (acc + 2)) =
            cyclicTwoThreeState
              (acc + weightSum weight (x :: xs))
        rw [ih (acc + 2) (by omega)]
        simp [weightSum, hx]
        congr 1
        omega

private theorem cyclicTwoThreeEval_weighted
    (weight : Nat → Nat)
    (oneOrTwo : ∀ x, weight x = 1 ∨ weight x = 2)
    (w : Word Nat) :
    cyclicTwoThree.semigroup.eval (weightedValuation weight) w =
      cyclicTwoThreeState (weightSum weight w.toList) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicTwoThreeMul current (weightedValuation weight x))
            (weightedValuation weight head) =
          cyclicTwoThreeState
            (weightSum weight (head :: tail))
      rw [show weightedValuation weight head =
          cyclicTwoThreeState (weight head) by rfl]
      have headPos : 0 < weight head := by
        rcases oneOrTwo head with h | h <;> omega
      rw [cyclicTwoThreeFold_weighted weight oneOrTwo tail
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

private theorem cyclicTwoThreeEval_unit (w : Word Nat) :
    cyclicTwoThree.semigroup.eval (weightedValuation unitWeight) w =
      cyclicTwoThreeState w.toList.length := by
  rw [cyclicTwoThreeEval_weighted unitWeight (by
    intro x
    exact Or.inl rfl)]
  rw [weightSum_unit]

private theorem cyclicTwoThreeEval_doubled (z : Nat) (w : Word Nat) :
    cyclicTwoThree.semigroup.eval
        (weightedValuation (doubledWeight z)) w =
      cyclicTwoThreeState (w.toList.length + w.toList.count z) := by
  rw [cyclicTwoThreeEval_weighted (doubledWeight z) (by
    intro x
    by_cases hx : x = z
    · exact Or.inr (by simp [doubledWeight, hx])
    · exact Or.inl (by simp [doubledWeight, hx]))]
  rw [weightSum_doubled]

private theorem cyclicTwoThreeState_eq_one {n : Nat} :
    cyclicTwoThreeState n = cyclicTwoThreeState 1 ↔ n = 1 := by
  constructor
  · intro h
    by_cases hn1 : n = 1
    · exact hn1
    · by_cases h0 : n % 3 = 0
      · simp [cyclicTwoThreeState, hn1, h0] at h
      · by_cases h1 : n % 3 = 1
        · simp [cyclicTwoThreeState, hn1, h1] at h
        · have h2 : n % 3 = 2 := by omega
          simp [cyclicTwoThreeState, hn1, h2] at h
  · intro h
    rw [h]

private theorem cyclicTwoThreeState_long_mod_three
    {m n : Nat} (mLong : 2 ≤ m) (nLong : 2 ≤ n)
    (h : cyclicTwoThreeState m = cyclicTwoThreeState n) :
    m % 3 = n % 3 := by
  have hm1 : m ≠ 1 := by omega
  have hn1 : n ≠ 1 := by omega
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;>
    rcases hn with hn | hn | hn
  · omega
  · simp [cyclicTwoThreeState, hm1, hn1, hm, hn] at h
  · simp [cyclicTwoThreeState, hm1, hn1, hm, hn] at h
  · simp [cyclicTwoThreeState, hm1, hn1, hm, hn] at h
  · omega
  · simp [cyclicTwoThreeState, hm1, hn1, hm, hn] at h
  · simp [cyclicTwoThreeState, hm1, hn1, hm, hn] at h
  · simp [cyclicTwoThreeState, hm1, hn1, hm, hn] at h
  · omega

private theorem cyclicTwoThreeState_one_add_injective
    {m n : Nat} (mLe : m ≤ 1) (nLe : n ≤ 1)
    (h :
      cyclicTwoThreeState (1 + m) =
        cyclicTwoThreeState (1 + n)) :
    m = n := by
  have hm : m = 0 ∨ m = 1 := by omega
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hm with rfl | rfl <;>
    rcases hn with rfl | rfl <;>
    simp [cyclicTwoThreeState] at h ⊢

def cyclicTwoThreeFiniteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def cyclicTwoThreeFiniteLongCancellationLaw : Identity (Fin 3) :=
  ⟨⟨0, [0, 0, 1, 2]⟩, ⟨1, [2]⟩⟩

theorem cyclicTwoThreeFiniteCommutativityLaw_map :
    cyclicTwoThreeFiniteCommutativityLaw.map Fin.val =
      cyclicTwoThreeCommutativityLaw := rfl

theorem cyclicTwoThreeFiniteLongCancellationLaw_map :
    cyclicTwoThreeFiniteLongCancellationLaw.map Fin.val =
      cyclicTwoThreeLongCancellationLaw := rfl

set_option maxRecDepth 100000 in
theorem cyclicTwoThreeBasis_models :
    Models cyclicTwoThree.semigroup cyclicTwoThreeBasis := by
  intro e he
  simp only [cyclicTwoThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rw [← cyclicTwoThreeFiniteCommutativityLaw_map]
    exact cyclicTwoThree.checkIdentityNat_sound
      cyclicTwoThreeFiniteCommutativityLaw (by decide)
  · rw [← cyclicTwoThreeFiniteLongCancellationLaw_map]
    exact cyclicTwoThree.checkIdentityNat_sound
      cyclicTwoThreeFiniteLongCancellationLaw (by decide)

/-- Unrestricted completeness over `Nat` variables. One-letter words retain
their exact variable. At length at least two, weighted evaluations recover the
exponent vector modulo three, and the contextual cyclic-group replay derives
exactly those equalities. -/
theorem cyclicTwoThreeBasis_complete :
    BasisFor cyclicTwoThree.semigroup cyclicTwoThreeBasis := by
  refine ⟨cyclicTwoThreeBasis_models, ?_⟩
  intro e valid
  have lengthState :
      cyclicTwoThreeState e.lhs.toList.length =
        cyclicTwoThreeState e.rhs.toList.length := by
    have evaluated := valid (weightedValuation unitWeight)
    rw [cyclicTwoThreeEval_unit, cyclicTwoThreeEval_unit] at evaluated
    exact evaluated
  have weightedState :
      ∀ z,
        cyclicTwoThreeState
            (e.lhs.toList.length + e.lhs.toList.count z) =
          cyclicTwoThreeState
            (e.rhs.toList.length + e.rhs.toList.count z) := by
    intro z
    have evaluated := valid (weightedValuation (doubledWeight z))
    rw [cyclicTwoThreeEval_doubled,
      cyclicTwoThreeEval_doubled] at evaluated
    exact evaluated
  have lhsPos : 0 < e.lhs.toList.length := by
    cases e.lhs
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    cases e.rhs
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      apply cyclicTwoThreeState_eq_one.mp
      rw [← lengthState, lhsOne]
    have countEq : ∀ z,
        e.lhs.toList.count z = e.rhs.toList.count z := by
      intro z
      apply cyclicTwoThreeState_one_add_injective
      · simpa [lhsOne] using
          (List.count_le_length (a := z) (l := e.lhs.toList))
      · simpa [rhsOne] using
          (List.count_le_length (a := z) (l := e.rhs.toList))
      · simpa [lhsOne, rhsOne] using weightedState z
    exact cyclicTwoThreeDerivesPermutation e.lhs e.rhs <|
      List.perm_iff_count.mpr countEq
  · have lhsLong : 2 ≤ e.lhs.toList.length := by omega
    have rhsNotOne : e.rhs.toList.length ≠ 1 := by
      intro rhsOne
      have lhsStateOne :
          cyclicTwoThreeState e.lhs.toList.length =
            cyclicTwoThreeState 1 := by
        rw [lengthState, rhsOne]
      exact lhsOne <|
        cyclicTwoThreeState_eq_one.mp lhsStateOne
    have rhsLong : 2 ≤ e.rhs.toList.length := by omega
    have lengthMod :
        e.lhs.toList.length % 3 =
          e.rhs.toList.length % 3 :=
      cyclicTwoThreeState_long_mod_three lhsLong rhsLong lengthState
    have modEq :
        ∀ z,
          e.lhs.toList.count z % 3 =
            e.rhs.toList.count z % 3 := by
      intro z
      have totalMod :=
        cyclicTwoThreeState_long_mod_three
          (m := e.lhs.toList.length + e.lhs.toList.count z)
          (n := e.rhs.toList.length + e.rhs.toList.count z)
          (by omega) (by omega) (weightedState z)
      rw [Nat.add_mod, Nat.add_mod] at totalMod
      omega
    exact cyclicTwoThreeDerivesLongModThree
      e.lhs e.rhs lhsLong rhsLong modEq

theorem cyclicTwoThree_selfDual :
    cyclicTwoThree.semigroup.opposite = cyclicTwoThree.semigroup := by
  unfold cyclicTwoThree FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  decide +revert

theorem cyclicTwoThreeOppositeBasis_complete :
    BasisFor cyclicTwoThree.semigroup.opposite cyclicTwoThreeBasis := by
  rw [cyclicTwoThree_selfDual]
  exact cyclicTwoThreeBasis_complete

end SemigroupBasis.Examples

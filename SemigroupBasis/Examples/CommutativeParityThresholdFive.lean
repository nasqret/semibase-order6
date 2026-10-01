import SemigroupBasis.Examples.CommutativeParityThree
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The zero-based multiplication table of the stored representative
`S5_222`:
`[[1,1,3,1,1],[1,1,3,1,1],[3,3,1,3,3],
  [1,1,3,2,1],[1,1,3,1,5]]`. -/
def commutativeParityThresholdFiveMul (a b : Fin 5) : Fin 5 :=
  if a = 0 then
    if b = 2 then 2 else 0
  else if a = 1 then
    if b = 2 then 2 else 0
  else if a = 2 then
    if b = 2 then 0 else 2
  else if a = 3 then
    if b = 2 then 2 else if b = 3 then 1 else 0
  else
    if b = 2 then 2 else if b = 4 then 4 else 0

/-- The five-element commutative semigroup `S5_222`. -/
def commutativeParityThresholdFive : FiniteTable where
  order := 5
  mul := commutativeParityThresholdFiveMul
  assoc := by decide

def parityThresholdXY : Word Nat := ⟨0, [1]⟩
def parityThresholdYX : Word Nat := ⟨1, [0]⟩
def parityThresholdXXX : Word Nat := ⟨0, [0, 0]⟩
def parityThresholdXXXXX : Word Nat := ⟨0, [0, 0, 0, 0]⟩
def parityThresholdXXY : Word Nat := ⟨0, [0, 1]⟩
def parityThresholdXXXXY : Word Nat := ⟨0, [0, 0, 0, 1]⟩
def parityThresholdXXYYY : Word Nat := ⟨0, [0, 1, 1, 1]⟩
def parityThresholdXYZ : Word Nat := ⟨0, [1, 2]⟩
def parityThresholdXXXYZ : Word Nat := ⟨0, [0, 0, 1, 2]⟩

def parityThresholdCommutativityLaw : Identity Nat :=
  ⟨parityThresholdXY, parityThresholdYX⟩

def parityThresholdUnaryLaw : Identity Nat :=
  ⟨parityThresholdXXX, parityThresholdXXXXX⟩

def parityThresholdLeftHeavyLaw : Identity Nat :=
  ⟨parityThresholdXXY, parityThresholdXXXXY⟩

def parityThresholdRightHeavyLaw : Identity Nat :=
  ⟨parityThresholdXXY, parityThresholdXXYYY⟩

def parityThresholdLongLaw : Identity Nat :=
  ⟨parityThresholdXYZ, parityThresholdXXXYZ⟩

/-- The exact catalogue basis
`xy = yx`, `xxx = xxxxx`, `xxy = xxxxy`, `xxy = xxyyy`,
`xyz = xxxyz`. The three specialized power laws are substitution
instances of the final law, but remain in the stored basis. -/
def commutativeParityThresholdFiveBasis : List (Identity Nat) :=
  [parityThresholdCommutativityLaw, parityThresholdUnaryLaw,
    parityThresholdLeftHeavyLaw, parityThresholdRightHeavyLaw,
    parityThresholdLongLaw]

private def instantiateThreeWords
    (u v w : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | 2 => w
  | n + 3 => Word.singleton (n + 3)

theorem parityThresholdDerivesCommutativity (u v : Word Nat) :
    Derives commutativeParityThresholdFiveBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativeParityThresholdFiveBasis
        parityThresholdXY parityThresholdYX :=
    Derives.fromBasis (e := parityThresholdCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v v)
  simpa [commutativeParityThresholdFiveBasis,
    parityThresholdCommutativityLaw, parityThresholdXY,
    parityThresholdYX, instantiateThreeWords, Word.bind, Word.append,
    Word.singleton] using h

/-- Insert two additional copies of the first nonempty factor while retaining
two nonempty contextual factors. -/
theorem parityThresholdDerivesLongInsertion
    (u v w : Word Nat) :
    Derives commutativeParityThresholdFiveBasis
      ((u ++ v) ++ w) ((((u ++ u) ++ u) ++ v) ++ w) := by
  have hbase :
      Derives commutativeParityThresholdFiveBasis
        parityThresholdXYZ parityThresholdXXXYZ :=
    Derives.fromBasis (e := parityThresholdLongLaw) <| by
      exact List.Mem.tail _ <| List.Mem.tail _ <|
        List.Mem.tail _ <| List.Mem.tail _ <| List.Mem.head _
  have h := Derives.subst hbase (instantiateThreeWords u v w)
  simpa [commutativeParityThresholdFiveBasis, parityThresholdLongLaw,
    parityThresholdXYZ, parityThresholdXXXYZ, instantiateThreeWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativeParityThresholdFiveBasis
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
              parityThresholdDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (parityThresholdDerivesCommutativity
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

theorem parityThresholdDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativeParityThresholdFiveBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Support and coordinate parity are the complete syntactic invariants for
the ordinary commutative parity basis. -/
private theorem parityDerivesOfSupportParity
    (u v : Word Nat)
    (supportEq : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parityEq :
      ∀ z, u.toList.count z % 2 = v.toList.count z % 2) :
    Derives commutativeParityBasis u v := by
  have reducedPerm :
      (positiveParityReduce u.toList).Perm
        (positiveParityReduce v.toList) :=
    positiveParityReduce_perm supportEq parityEq
  have lhsNormal := positiveParityDerivesNormal u
  have rhsNormal := positiveParityDerivesNormal v
  cases hl : positiveParityReduce u.toList with
  | nil =>
      have present :
          u.head ∈ positiveParityReduce u.toList :=
        (mem_positiveParityReduce_iff _ _).mpr
          (by simp [Word.toList])
      exact False.elim (by simpa [hl] using present)
  | cons x xs =>
      cases hr : positiveParityReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (parityDerivesPermutation
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

/-- The parity law `u = uuu` is available after a product of two nonempty
markers. -/
theorem parityThresholdDerivesContextPower
    (a b u : Word Nat) :
    Derives commutativeParityThresholdFiveBasis
      ((a ++ b) ++ u) ((a ++ b) ++ ((u ++ u) ++ u)) := by
  have enter :=
    parityThresholdDerivesCommutativity (a ++ b) u
  have expand :=
    parityThresholdDerivesLongInsertion u a b
  have exit :=
    parityThresholdDerivesCommutativity ((u ++ u) ++ u) (a ++ b)
  exact Derives.trans enter <|
    Derives.trans
      (by simpa [Word.append_assoc] using expand)
      (by simpa [Word.append_assoc] using exit)

/-- Replay a derivation from `x = xxx`, `xy = yx` after two fixed nonempty
markers. Those markers supply the two residual factors required by
`xyz = xxxyz`. -/
theorem parityThresholdLiftParity
    {u v : Word Nat}
    (h : Derives commutativeParityBasis u v)
    (a b : Word Nat) (σ : Nat → Word Nat) :
    Derives commutativeParityThresholdFiveBasis
      ((a ++ b) ++ u.bind σ)
      ((a ++ b) ++ v.bind σ) := by
  induction h generalizing a b σ with
  | fromBasis hmem =>
      simp only [commutativeParityBasis, List.mem_cons,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · simpa [parityPowerLaw, parityX, parityXXX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          parityThresholdDerivesContextPower a b (σ 0)
      · have commute :=
          parityThresholdDerivesCommutativity (σ 0) (σ 1)
        simpa [parityCommutativityLaw, parityXY, parityYX, Word.bind,
          Word.append, Word.singleton, Word.append_assoc] using
          Derives.prepend (a ++ b) commute
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

private def frontedWord (z : Nat) (w : Word Nat) : Word Nat :=
  wordOfCons z (w.toList.erase z)

private theorem word_perm_frontedWord
    (z : Nat) (w : Word Nat) (present : z ∈ w.toList) :
    w.toList.Perm (frontedWord z w).toList := by
  simpa [frontedWord, wordOfCons, Word.toList] using
    List.perm_cons_erase present

private theorem parityThresholdDerivesHeadExpansion
    (z a b : Nat) (rest : List Nat) :
    Derives commutativeParityThresholdFiveBasis
      (wordOfCons z (a :: b :: rest))
      ((Word.singleton z ++ Word.singleton z) ++
        wordOfCons z (a :: b :: rest)) := by
  simpa [wordOfCons, Word.singleton, Word.append,
    Word.append_assoc] using
    parityThresholdDerivesLongInsertion
      (Word.singleton z) (Word.singleton a) (wordOfCons b rest)

/-- Every pair of words of length at least three with equal support and equal
coordinate parity is derivably equal. A common supported variable is moved
to the front of both words, doubled as the fixed marker pair, and then the
ordinary parity derivation is replayed between those markers. -/
theorem parityThresholdDerivesLongSupportParity
    (u v : Word Nat)
    (uLong : 3 ≤ u.toList.length)
    (vLong : 3 ≤ v.toList.length)
    (supportEq : ∀ z, z ∈ u.toList ↔ z ∈ v.toList)
    (parityEq :
      ∀ z, u.toList.count z % 2 = v.toList.count z % 2) :
    Derives commutativeParityThresholdFiveBasis u v := by
  let marker := u.head
  have markerInU : marker ∈ u.toList := by
    simp [marker, Word.toList]
  have markerInV : marker ∈ v.toList :=
    (supportEq marker).mp markerInU
  let uFront := frontedWord marker u
  let vFront := frontedWord marker v
  have uPerm : u.toList.Perm uFront.toList :=
    word_perm_frontedWord marker u markerInU
  have vPerm : v.toList.Perm vFront.toList :=
    word_perm_frontedWord marker v markerInV
  have uToFront :=
    parityThresholdDerivesPermutation u uFront uPerm
  have vToFront :=
    parityThresholdDerivesPermutation v vFront vPerm
  have uCount :
      ∀ z, u.toList.count z = uFront.toList.count z :=
    List.perm_iff_count.mp uPerm
  have vCount :
      ∀ z, v.toList.count z = vFront.toList.count z :=
    List.perm_iff_count.mp vPerm
  have frontSupport :
      ∀ z, z ∈ uFront.toList ↔ z ∈ vFront.toList := by
    intro z
    rw [← List.count_pos_iff, ← List.count_pos_iff,
      ← uCount z, ← vCount z, List.count_pos_iff,
      List.count_pos_iff]
    exact supportEq z
  have frontParity :
      ∀ z,
        uFront.toList.count z % 2 =
          vFront.toList.count z % 2 := by
    intro z
    rw [← uCount z, ← vCount z]
    exact parityEq z
  have parityDerivation :=
    parityDerivesOfSupportParity
      uFront vFront frontSupport frontParity
  have lifted :=
    parityThresholdLiftParity parityDerivation
      (Word.singleton marker) (Word.singleton marker) Word.singleton
  rw [bind_singleton, bind_singleton] at lifted
  cases hu : u.toList.erase marker with
  | nil =>
      have eraseLength := List.length_erase_of_mem markerInU
      rw [hu] at eraseLength
      simp at eraseLength
      omega
  | cons ua ut =>
      cases ut with
      | nil =>
          have eraseLength := List.length_erase_of_mem markerInU
          rw [hu] at eraseLength
          simp at eraseLength
          omega
      | cons ub ur =>
          cases hv : v.toList.erase marker with
          | nil =>
              have eraseLength := List.length_erase_of_mem markerInV
              rw [hv] at eraseLength
              simp at eraseLength
              omega
          | cons va vt =>
              cases vt with
              | nil =>
                  have eraseLength := List.length_erase_of_mem markerInV
                  rw [hv] at eraseLength
                  simp at eraseLength
                  omega
              | cons vb vr =>
                  have expandU :
                      Derives commutativeParityThresholdFiveBasis
                        uFront
                        ((Word.singleton marker ++
                            Word.singleton marker) ++ uFront) := by
                    simpa [uFront, frontedWord, hu] using
                      parityThresholdDerivesHeadExpansion
                        marker ua ub ur
                  have expandV :
                      Derives commutativeParityThresholdFiveBasis
                        vFront
                        ((Word.singleton marker ++
                            Word.singleton marker) ++ vFront) := by
                    simpa [vFront, frontedWord, hv] using
                      parityThresholdDerivesHeadExpansion
                        marker va vb vr
                  exact Derives.trans uToFront <|
                    Derives.trans expandU <|
                    Derives.trans lifted <|
                    Derives.trans (Derives.symm expandV)
                      (Derives.symm vToFront)

def parityThresholdFiniteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def parityThresholdFiniteUnaryLaw : Identity (Fin 1) :=
  ⟨⟨0, [0, 0]⟩, ⟨0, [0, 0, 0, 0]⟩⟩

def parityThresholdFiniteLeftHeavyLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩⟩

def parityThresholdFiniteRightHeavyLaw : Identity (Fin 2) :=
  ⟨⟨0, [0, 1]⟩, ⟨0, [0, 1, 1, 1]⟩⟩

def parityThresholdFiniteLongLaw : Identity (Fin 3) :=
  ⟨⟨0, [1, 2]⟩, ⟨0, [0, 0, 1, 2]⟩⟩

theorem parityThresholdFiniteCommutativityLaw_map :
    parityThresholdFiniteCommutativityLaw.map Fin.val =
      parityThresholdCommutativityLaw := rfl

theorem parityThresholdFiniteUnaryLaw_map :
    parityThresholdFiniteUnaryLaw.map Fin.val =
      parityThresholdUnaryLaw := rfl

theorem parityThresholdFiniteLeftHeavyLaw_map :
    parityThresholdFiniteLeftHeavyLaw.map Fin.val =
      parityThresholdLeftHeavyLaw := rfl

theorem parityThresholdFiniteRightHeavyLaw_map :
    parityThresholdFiniteRightHeavyLaw.map Fin.val =
      parityThresholdRightHeavyLaw := rfl

theorem parityThresholdFiniteLongLaw_map :
    parityThresholdFiniteLongLaw.map Fin.val =
      parityThresholdLongLaw := rfl

set_option maxRecDepth 100000 in
theorem commutativeParityThresholdFiveBasis_models :
    Models commutativeParityThresholdFive.semigroup
      commutativeParityThresholdFiveBasis := by
  intro e he
  simp only [commutativeParityThresholdFiveBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · rw [← parityThresholdFiniteCommutativityLaw_map]
    exact commutativeParityThresholdFive.checkIdentityNat_sound
      parityThresholdFiniteCommutativityLaw (by decide)
  · rw [← parityThresholdFiniteUnaryLaw_map]
    exact commutativeParityThresholdFive.checkIdentityNat_sound
      parityThresholdFiniteUnaryLaw (by decide)
  · rw [← parityThresholdFiniteLeftHeavyLaw_map]
    exact commutativeParityThresholdFive.checkIdentityNat_sound
      parityThresholdFiniteLeftHeavyLaw (by decide)
  · rw [← parityThresholdFiniteRightHeavyLaw_map]
    exact commutativeParityThresholdFive.checkIdentityNat_sound
      parityThresholdFiniteRightHeavyLaw (by decide)
  · rw [← parityThresholdFiniteLongLaw_map]
    exact commutativeParityThresholdFive.checkIdentityNat_sound
      parityThresholdFiniteLongLaw (by decide)

private def supportSeparator (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then 0 else 4

private def supportState (n : Nat) : Fin 5 :=
  if n = 0 then 4 else 0

private theorem supportMul_target (n : Nat) :
    commutativeParityThresholdFiveMul (supportState n) 0 =
      supportState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, commutativeParityThresholdFiveMul, hn]

private theorem supportMul_other (n : Nat) :
    commutativeParityThresholdFiveMul (supportState n) 4 =
      supportState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · simp [supportState, commutativeParityThresholdFiveMul, hn]

private theorem supportFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commutativeParityThresholdFiveMul current
            (supportSeparator z x))
        (supportState acc) =
      supportState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show supportSeparator z z = (0 : Fin 5) by
          simp [supportSeparator]]
        rw [supportMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show supportSeparator z x = (4 : Fin 5) by
          simp [supportSeparator, hx]]
        rw [supportMul_other, ih]

private theorem parityThresholdEval_supportSeparator
    (z : Nat) (w : Word Nat) :
    commutativeParityThresholdFive.semigroup.eval
        (supportSeparator z) w =
      supportState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commutativeParityThresholdFiveMul current
                (supportSeparator z x))
            (supportSeparator z head) =
          supportState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show supportSeparator z z = supportState 1 by
          apply Fin.ext
          simp [supportSeparator, supportState]]
        rw [supportFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show supportSeparator z head = supportState 0 by
          apply Fin.ext
          simp [supportSeparator, supportState, hhead]]
        rw [supportFold]
        congr 1
        omega

theorem parityThresholdValid_support
    (e : Identity Nat)
    (valid : e.SatisfiedBy
      commutativeParityThresholdFive.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (supportSeparator z)
  rw [parityThresholdEval_supportSeparator,
    parityThresholdEval_supportSeparator] at evaluated
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have hlne : e.lhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hl)
    have hrzero : e.rhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hr
    simp [supportState, hlne, hrzero] at evaluated
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have hrne : e.rhs.toList.count z ≠ 0 :=
      Nat.ne_of_gt (List.count_pos_iff.mpr hr)
    have hlzero : e.lhs.toList.count z = 0 :=
      List.count_eq_zero.mpr hl
    simp [supportState, hlzero, hrne] at evaluated

private def paritySeparator (z : Nat) : Nat → Fin 5 :=
  fun x => if x = z then 2 else 4

private def parityState (n : Nat) : Fin 5 :=
  if n = 0 then 4 else if n % 2 = 0 then 0 else 2

private theorem parityMul_target (n : Nat) :
    commutativeParityThresholdFiveMul (parityState n) 2 =
      parityState (n + 1) := by
  by_cases hn : n = 0
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · have hnext : (n + 1) % 2 = 1 := by omega
      simp [parityState, commutativeParityThresholdFiveMul,
        hn, hp, hnext]
    · have hmod : n % 2 = 1 := by omega
      have hnext : (n + 1) % 2 = 0 := by omega
      simp [parityState, commutativeParityThresholdFiveMul,
        hn, hmod, hnext]

private theorem parityMul_other (n : Nat) :
    commutativeParityThresholdFiveMul (parityState n) 4 =
      parityState n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · by_cases hp : n % 2 = 0
    · simp [parityState, commutativeParityThresholdFiveMul, hn, hp]
    · have hmod : n % 2 = 1 := by omega
      simp [parityState, commutativeParityThresholdFiveMul, hn, hmod]

private theorem parityFold
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commutativeParityThresholdFiveMul current
            (paritySeparator z x))
        (parityState acc) =
      parityState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show paritySeparator z z = (2 : Fin 5) by
          simp [paritySeparator]]
        rw [parityMul_target, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show paritySeparator z x = (4 : Fin 5) by
          simp [paritySeparator, hx]]
        rw [parityMul_other, ih]

private theorem parityThresholdEval_paritySeparator
    (z : Nat) (w : Word Nat) :
    commutativeParityThresholdFive.semigroup.eval
        (paritySeparator z) w =
      parityState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commutativeParityThresholdFiveMul current
                (paritySeparator z x))
            (paritySeparator z head) =
          parityState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show paritySeparator z z = parityState 1 by
          apply Fin.ext
          simp [paritySeparator, parityState]]
        rw [parityFold]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show paritySeparator z head = parityState 0 by
          apply Fin.ext
          simp [paritySeparator, parityState, hhead]]
        rw [parityFold]
        congr 1
        omega

theorem parityThresholdValid_parity
    (e : Identity Nat)
    (valid : e.SatisfiedBy
      commutativeParityThresholdFive.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 =
      e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (paritySeparator z)
  rw [parityThresholdEval_paritySeparator,
    parityThresholdEval_paritySeparator] at evaluated
  have supportEq := parityThresholdValid_support e valid z
  by_cases hl : e.lhs.toList.count z = 0
  · have hr : e.rhs.toList.count z = 0 := by
      rw [List.count_eq_zero]
      exact fun h => (List.count_eq_zero.mp hl) (supportEq.mpr h)
    simp [hl, hr]
  · have hr : e.rhs.toList.count z ≠ 0 := by
      have lhsMem : z ∈ e.lhs.toList :=
        List.count_pos_iff.mp (Nat.pos_of_ne_zero hl)
      exact Nat.ne_of_gt <|
        List.count_pos_iff.mpr (supportEq.mp lhsMem)
    have specialized := evaluated
    simp only [parityState, if_neg hl, if_neg hr] at specialized
    by_cases hlp : e.lhs.toList.count z % 2 = 0
    · by_cases hrp : e.rhs.toList.count z % 2 = 0
      · exact hlp.trans hrp.symm
      · simp [hlp, hrp] at specialized
    · have hlmod : e.lhs.toList.count z % 2 = 1 := by omega
      by_cases hrp : e.rhs.toList.count z % 2 = 0
      · simp [hlmod, hrp] at specialized
      · have hrmod : e.rhs.toList.count z % 2 = 1 := by omega
        exact hlmod.trans hrmod.symm

private def lengthSeparator : Nat → Fin 5 := fun _ => 3

private def lengthState (n : Nat) : Fin 5 :=
  if n = 1 then 3 else if n = 2 then 1 else 0

private theorem lengthMul_three (n : Nat) (nPos : 0 < n) :
    commutativeParityThresholdFiveMul (lengthState n) 3 =
      lengthState (n + 1) := by
  by_cases hn1 : n = 1
  · subst n
    rfl
  · by_cases hn2 : n = 2
    · subst n
      rfl
    · have hn3 : 3 ≤ n := by omega
      simp [lengthState, commutativeParityThresholdFiveMul,
        hn1, hn2, show n ≠ 0 by omega,
        show n + 1 ≠ 2 by omega]

private theorem lengthFold
    (xs : List Nat) (acc : Nat) (accPos : 0 < acc) :
    xs.foldl
        (fun current _ =>
          commutativeParityThresholdFiveMul current 3)
        (lengthState acc) =
      lengthState (acc + xs.length) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [lengthMul_three acc accPos, ih (acc + 1) (by omega)]
      congr 1
      omega

private theorem parityThresholdEval_lengthSeparator
    (w : Word Nat) :
    commutativeParityThresholdFive.semigroup.eval
        lengthSeparator w =
      lengthState w.toList.length := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current _ =>
              commutativeParityThresholdFiveMul current 3) 3 =
          lengthState (head :: tail).length
      simpa [lengthState, Nat.add_comm] using
        lengthFold tail 1 (by omega)

private theorem lengthState_capped_injective
    {m n : Nat} (mPos : 0 < m) (nPos : 0 < n)
    (equal : lengthState m = lengthState n) :
    min m 3 = min n 3 := by
  have values := congrArg Fin.val equal
  by_cases hm1 : m = 1
  · subst m
    by_cases hn1 : n = 1
    · subst n
      rfl
    · by_cases hn2 : n = 2
      · subst n
        simp [lengthState] at values
        omega
      · have hn3 : 3 ≤ n := by omega
        simp [lengthState, hn1, hn2] at values
  · by_cases hm2 : m = 2
    · subst m
      by_cases hn1 : n = 1
      · subst n
        simp [lengthState] at values
        omega
      · by_cases hn2 : n = 2
        · subst n
          rfl
        · have hn3 : 3 ≤ n := by omega
          simp [lengthState, hn1, hn2] at values
    · have hm3 : 3 ≤ m := by omega
      by_cases hn1 : n = 1
      · subst n
        simp [lengthState, hm1, hm2] at values
        omega
      · by_cases hn2 : n = 2
        · subst n
          simp [lengthState, hm1, hm2] at values
        · have hn3 : 3 ≤ n := by omega
          simp [Nat.min_eq_right (by omega : 3 ≤ m),
            Nat.min_eq_right (by omega : 3 ≤ n)]

theorem parityThresholdValid_capped_length
    (e : Identity Nat)
    (valid : e.SatisfiedBy
      commutativeParityThresholdFive.semigroup) :
    min e.lhs.toList.length 3 =
      min e.rhs.toList.length 3 := by
  have evaluated := valid lengthSeparator
  rw [parityThresholdEval_lengthSeparator,
    parityThresholdEval_lengthSeparator] at evaluated
  exact lengthState_capped_injective
    (by simp [Word.toList]) (by simp [Word.toList]) evaluated

private theorem short_perm_of_support_parity
    {xs ys : List Nat}
    (xsBound : xs.length ≤ 2)
    (ysBound : ys.length ≤ 2)
    (supportEq : ∀ z, z ∈ xs ↔ z ∈ ys)
    (parityEq : ∀ z, xs.count z % 2 = ys.count z % 2) :
    xs.Perm ys := by
  rw [List.perm_iff_count]
  intro z
  have leftBound := List.count_le_length (a := z) (l := xs)
  have rightBound := List.count_le_length (a := z) (l := ys)
  have positiveEq : 0 < xs.count z ↔ 0 < ys.count z := by
    rw [List.count_pos_iff, List.count_pos_iff]
    exact supportEq z
  have parity := parityEq z
  omega

/-- Unrestricted completeness over `Nat` variables. Lengths one and two
retain their exact multisets. At length at least three, support and coordinate
parity are complete invariants. -/
theorem commutativeParityThresholdFiveBasis_complete :
    BasisFor commutativeParityThresholdFive.semigroup
      commutativeParityThresholdFiveBasis := by
  refine ⟨commutativeParityThresholdFiveBasis_models, ?_⟩
  intro e valid
  have supportEq := parityThresholdValid_support e valid
  have parityEq := parityThresholdValid_parity e valid
  have cappedLength := parityThresholdValid_capped_length e valid
  have lhsPos : 0 < e.lhs.toList.length := by
    simp [Word.toList]
  have rhsPos : 0 < e.rhs.toList.length := by
    simp [Word.toList]
  by_cases lhsOne : e.lhs.toList.length = 1
  · have rhsOne : e.rhs.toList.length = 1 := by
      omega
    exact parityThresholdDerivesPermutation e.lhs e.rhs <|
      short_perm_of_support_parity (by omega) (by omega)
        supportEq parityEq
  · by_cases lhsTwo : e.lhs.toList.length = 2
    · have rhsTwo : e.rhs.toList.length = 2 := by
        omega
      exact parityThresholdDerivesPermutation e.lhs e.rhs <|
        short_perm_of_support_parity (by omega) (by omega)
          supportEq parityEq
    · have lhsLong : 3 ≤ e.lhs.toList.length := by omega
      have rhsLong : 3 ≤ e.rhs.toList.length := by omega
      exact parityThresholdDerivesLongSupportParity
        e.lhs e.rhs lhsLong rhsLong supportEq parityEq

theorem commutativeParityThresholdFiveOppositeBasis_complete :
    BasisFor commutativeParityThresholdFive.semigroup.opposite
      (reversedBasis commutativeParityThresholdFiveBasis) :=
  commutativeParityThresholdFiveBasis_complete.oppositeReversed

end SemigroupBasis.Examples

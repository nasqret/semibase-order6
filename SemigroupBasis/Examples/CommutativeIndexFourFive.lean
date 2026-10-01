import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

def indexFourFiveXY : Word Nat := ⟨0, [1]⟩
def indexFourFiveYX : Word Nat := ⟨1, [0]⟩
def indexFourFiveXXXX : Word Nat := ⟨0, [0, 0, 0]⟩
def indexFourFiveXXXXX : Word Nat := ⟨0, [0, 0, 0, 0]⟩

def indexFourFiveCommutativityLaw : Identity Nat :=
  ⟨indexFourFiveXY, indexFourFiveYX⟩

def indexFourFivePowerLaw : Identity Nat :=
  ⟨indexFourFiveXXXX, indexFourFiveXXXXX⟩

/-- The exact commutative index-four, period-one basis
`xy = yx`, `xxxx = xxxxx`. -/
def commutativeIndexFourFiveBasis : List (Identity Nat) :=
  [indexFourFiveCommutativityLaw, indexFourFivePowerLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem indexFourFiveDerivesCommutativity (u v : Word Nat) :
    Derives commutativeIndexFourFiveBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativeIndexFourFiveBasis
        indexFourFiveXY indexFourFiveYX :=
    Derives.fromBasis (e := indexFourFiveCommutativityLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativeIndexFourFiveBasis,
    indexFourFiveCommutativityLaw, indexFourFiveXY, indexFourFiveYX,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using h

theorem indexFourFiveDerivesFiveContraction (u : Word Nat) :
    Derives commutativeIndexFourFiveBasis
      ((((u ++ u) ++ u) ++ u) ++ u)
      (((u ++ u) ++ u) ++ u) := by
  have hbase :
      Derives commutativeIndexFourFiveBasis
        indexFourFiveXXXXX indexFourFiveXXXX :=
    Derives.symm <|
      Derives.fromBasis (e := indexFourFivePowerLaw) <| by
        exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativeIndexFourFiveBasis, indexFourFivePowerLaw,
    indexFourFiveXXXXX, indexFourFiveXXXX, instantiateTwoWords,
    Word.bind, Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativeIndexFourFiveBasis
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
              indexFourFiveDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (indexFourFiveDerivesCommutativity
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

theorem indexFourFiveDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativeIndexFourFiveBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain at most four copies of every variable. -/
def capFourReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := capFourReduce xs
      if reduced.count x < 4 then x :: reduced else reduced

theorem count_capFourReduce (z : Nat) (xs : List Nat) :
    (capFourReduce xs).count z = min (xs.count z) 4 := by
  induction xs with
  | nil =>
      simp [capFourReduce]
  | cons x xs ih =>
      simp only [capFourReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx), ih]

private theorem capFourReduce_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    capFourReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_capFourReduce x (x :: xs)
  rw [hempty] at hcount
  simp at hcount
  omega

theorem capFourReduce_perm_of_capped_count_eq
    {xs ys : List Nat}
    (hcount : ∀ z, min (xs.count z) 4 = min (ys.count z) 4) :
    (capFourReduce xs).Perm (capFourReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_capFourReduce, count_capFourReduce, hcount z]

private theorem four_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 4) :
    xs.Perm
      (x :: x :: x :: x ::
        ((((xs.erase x).erase x).erase x).erase x)) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have hcount₁ : (xs.erase x).count x = 3 := by
    rw [List.count_erase_self]
    omega
  have hx₁ : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase hx₁
  have hcount₂ : ((xs.erase x).erase x).count x = 2 := by
    rw [List.count_erase_self]
    omega
  have hx₂ : x ∈ (xs.erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have third := List.perm_cons_erase hx₂
  have hcount₃ :
      (((xs.erase x).erase x).erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hx₃ : x ∈ ((xs.erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons x <|
    second.trans <| List.Perm.cons x <|
      third.trans <| List.Perm.cons x (List.perm_cons_erase hx₃)

private theorem contractLeadingFive :
    ∀ x xs,
      Derives commutativeIndexFourFiveBasis
        (wordOfCons x (x :: x :: x :: x :: xs))
        (wordOfCons x (x :: x :: x :: xs))
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          indexFourFiveDerivesFiveContraction (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (indexFourFiveDerivesFiveContraction (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem indexFourFiveDerivesNormalizeList :
    ∀ x xs,
      match capFourReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativeIndexFourFiveBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := indexFourFiveDerivesNormalizeList y ys
      cases hs : capFourReduce (y :: ys) with
      | nil =>
          exact False.elim (capFourReduce_cons_ne_nil y ys hs)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 4
          · have reduced :
                capFourReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (capFourReduce (y :: ys)).count x < 4 then
                  x :: capFourReduce (y :: ys)
                else capFourReduce (y :: ys)) = x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe :
                (z :: zs).count x ≤ 4 := by
              rw [← hs, count_capFourReduce]
              exact Nat.min_le_right _ _
            have countEq : (z :: zs).count x = 4 := by
              omega
            let remainder :=
              ((((z :: zs).erase x).erase x).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm
                  (x :: x :: x :: x :: remainder) := by
              simpa [remainder] using
                four_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm
                  (x :: x :: x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have arrangedToReduced :
                (x :: x :: x :: x :: remainder).Perm (z :: zs) :=
              suffixPerm.symm
            have arrange :
                Derives commutativeIndexFourFiveBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: x :: x :: remainder)) :=
              indexFourFiveDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFive x remainder
            have restore :
                Derives commutativeIndexFourFiveBasis
                  (wordOfCons x (x :: x :: x :: remainder))
                  (wordOfCons z zs) :=
              indexFourFiveDerivesPermutation _ _ arrangedToReduced
            have reduced :
                capFourReduce (x :: y :: ys) = z :: zs := by
              change
                (if (capFourReduce (y :: ys)).count x < 4 then
                  x :: capFourReduce (y :: ys)
                else capFourReduce (y :: ys)) = z :: zs
              rw [hs, if_neg hcount]
            rw [reduced]
            exact Derives.trans
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using prefixed)
              (Derives.trans arrange (Derives.trans contract restore))
termination_by
  _ xs => xs.length

theorem indexFourFiveDerivesNormal (w : Word Nat) :
    match capFourReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativeIndexFourFiveBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact indexFourFiveDerivesNormalizeList head tail

/-- Equality of every multiplicity after capping at four. -/
def SameCappedFour (u v : Word Nat) : Prop :=
  ∀ z, min (u.toList.count z) 4 = min (v.toList.count z) 4

theorem indexFourFiveDerives_of_sameCappedFour
    (u v : Word Nat) (same : SameCappedFour u v) :
    Derives commutativeIndexFourFiveBasis u v := by
  have reducedPerm :
      (capFourReduce u.toList).Perm (capFourReduce v.toList) :=
    capFourReduce_perm_of_capped_count_eq same
  have lhsNormal := indexFourFiveDerivesNormal u
  have rhsNormal := indexFourFiveDerivesNormal v
  cases hl : capFourReduce u.toList with
  | nil =>
      exact False.elim
        (capFourReduce_cons_ne_nil u.head u.tail (by
          simpa [Word.toList] using hl))
  | cons x xs =>
      cases hr : capFourReduce v.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (indexFourFiveDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

/-- Generic unrestricted completeness for `xy = yx`, `xxxx = xxxxx`.
A model only needs to separate all capped coordinate multiplicities. -/
theorem commutativeIndexFourFiveBasis_complete_of_separates
    (T : FiniteTable)
    (models : Models T.semigroup commutativeIndexFourFiveBasis)
    (separates :
      ∀ e : Identity Nat, e.SatisfiedBy T.semigroup →
        ∀ z, min (e.lhs.toList.count z) 4 =
          min (e.rhs.toList.count z) 4) :
    BasisFor T.semigroup commutativeIndexFourFiveBasis := by
  refine ⟨models, ?_⟩
  intro e valid
  exact indexFourFiveDerives_of_sameCappedFour
    e.lhs e.rhs (separates e valid)

end SemigroupBasis.Examples

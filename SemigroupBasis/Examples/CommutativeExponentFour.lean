import SemigroupBasis.Examples.CommutativeThresholdSupportFour

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based form of the `S4_40` table
`[[1,1,1,1],[1,1,1,2],[1,1,2,3],[1,2,3,4]]`. -/
def commutativeExponentFourMul (a b : Fin 4) : Fin 4 :=
  ⟨a.val + b.val - 3, by omega⟩

/-- The four-element commutative semigroup that records a selected variable's
multiplicity as zero, one, two, or at least three. -/
def commutativeExponentFour : FiniteTable where
  order := 4
  mul := commutativeExponentFourMul
  assoc := by decide

def exponentFourXY : Word Nat := ⟨0, [1]⟩
def exponentFourYX : Word Nat := ⟨1, [0]⟩
def exponentFourXXX : Word Nat := ⟨0, [0, 0]⟩
def exponentFourXXXX : Word Nat := ⟨0, [0, 0, 0]⟩

def exponentFourCommutativityLaw : Identity Nat :=
  ⟨exponentFourXY, exponentFourYX⟩

def exponentFourPowerLaw : Identity Nat :=
  ⟨exponentFourXXX, exponentFourXXXX⟩

/-- The basis `xy = yx`, `xxx = xxxx` of `S4_40`. -/
def commutativeExponentFourBasis : List (Identity Nat) :=
  [exponentFourCommutativityLaw, exponentFourPowerLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem exponentFourDerivesCommutativity (u v : Word Nat) :
    Derives commutativeExponentFourBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativeExponentFourBasis
        exponentFourXY exponentFourYX :=
    Derives.fromBasis (e := exponentFourCommutativityLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativeExponentFourBasis,
    exponentFourCommutativityLaw, exponentFourXY, exponentFourYX,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using h

theorem exponentFourDerivesFourContraction (u : Word Nat) :
    Derives commutativeExponentFourBasis
      (((u ++ u) ++ u) ++ u) ((u ++ u) ++ u) := by
  have hbase :
      Derives commutativeExponentFourBasis
        exponentFourXXXX exponentFourXXX :=
    Derives.symm <|
      Derives.fromBasis (e := exponentFourPowerLaw) <| by
        exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativeExponentFourBasis, exponentFourPowerLaw,
    exponentFourXXXX, exponentFourXXX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativeExponentFourBasis
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
              exponentFourDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (exponentFourDerivesCommutativity
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

theorem exponentFourDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativeExponentFourBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

private theorem exponentFourReduce_cons_ne_nil
    (x : Nat) (xs : List Nat) :
    capThreeReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_capThreeReduce x (x :: xs)
  rw [hempty] at hcount
  simp at hcount
  omega

private theorem three_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 3) :
    xs.Perm (x :: x :: x :: ((xs.erase x).erase x).erase x) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have hcount₁ : (xs.erase x).count x = 2 := by
    rw [List.count_erase_self]
    omega
  have hx₁ : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase hx₁
  have hcount₂ : ((xs.erase x).erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hx₂ : x ∈ (xs.erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons x <|
    second.trans <| List.Perm.cons x (List.perm_cons_erase hx₂)

private theorem contractLeadingFour :
    ∀ x xs,
      Derives commutativeExponentFourBasis
        (wordOfCons x (x :: x :: x :: xs))
        (wordOfCons x (x :: x :: xs))
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          exponentFourDerivesFourContraction (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (exponentFourDerivesFourContraction (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem exponentFourDerivesNormalizeList :
    ∀ x xs,
      match capThreeReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativeExponentFourBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := exponentFourDerivesNormalizeList y ys
      cases hs : capThreeReduce (y :: ys) with
      | nil =>
          exact False.elim (exponentFourReduce_cons_ne_nil y ys hs)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 3
          · have reduced :
                capThreeReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (capThreeReduce (y :: ys)).count x < 3 then
                  x :: capThreeReduce (y :: ys)
                else capThreeReduce (y :: ys)) = x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe :
                (z :: zs).count x ≤ 3 := by
              rw [← hs, count_capThreeReduce]
              exact Nat.min_le_right _ _
            have countEq : (z :: zs).count x = 3 := by omega
            let remainder := (((z :: zs).erase x).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm (x :: x :: x :: remainder) := by
              simpa [remainder] using
                three_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm
                  (x :: x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have arrangedToReduced :
                (x :: x :: x :: remainder).Perm (z :: zs) :=
              suffixPerm.symm
            have arrange :
                Derives commutativeExponentFourBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: x :: remainder)) :=
              exponentFourDerivesPermutation _ _ expandedPerm
            have contract := contractLeadingFour x remainder
            have restore :
                Derives commutativeExponentFourBasis
                  (wordOfCons x (x :: x :: remainder))
                  (wordOfCons z zs) :=
              exponentFourDerivesPermutation _ _ arrangedToReduced
            have reduced :
                capThreeReduce (x :: y :: ys) = z :: zs := by
              change
                (if (capThreeReduce (y :: ys)).count x < 3 then
                  x :: capThreeReduce (y :: ys)
                else capThreeReduce (y :: ys)) = z :: zs
              rw [hs, if_neg hcount]
            rw [reduced]
            exact Derives.trans
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using prefixed)
              (Derives.trans arrange (Derives.trans contract restore))
termination_by
  _ xs => xs.length

theorem exponentFourDerivesNormal (w : Word Nat) :
    match capThreeReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativeExponentFourBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact exponentFourDerivesNormalizeList head tail

theorem capThreeReduce_perm_of_capped_count_eq {xs ys : List Nat}
    (hcount : ∀ z, min (xs.count z) 3 = min (ys.count z) 3) :
    (capThreeReduce xs).Perm (capThreeReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_capThreeReduce, count_capThreeReduce, hcount z]

private def exponentFourState (n : Nat) : Fin 4 :=
  ⟨3 - min n 3, by omega⟩

private def exponentFourSeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 2 else 3

private theorem exponentFourMul_state_two (n : Nat) :
    commutativeExponentFourMul (exponentFourState n) 2 =
      exponentFourState (n + 1) := by
  apply Fin.ext
  simp [commutativeExponentFourMul, exponentFourState]
  omega

private theorem exponentFourMul_state_three (n : Nat) :
    commutativeExponentFourMul (exponentFourState n) 3 =
      exponentFourState n := by
  apply Fin.ext
  simp [commutativeExponentFourMul, exponentFourState]
  omega

private theorem exponentFourFold_separator
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commutativeExponentFourMul current
            (exponentFourSeparator z x))
        (exponentFourState acc) =
      exponentFourState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show exponentFourSeparator z z = (2 : Fin 4) by
          simp [exponentFourSeparator]]
        rw [exponentFourMul_state_two, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show exponentFourSeparator z x = (3 : Fin 4) by
          simp [exponentFourSeparator, hx]]
        rw [exponentFourMul_state_three, ih]

theorem exponentFourEval_separator (z : Nat) (w : Word Nat) :
    commutativeExponentFour.semigroup.eval
        (exponentFourSeparator z) w =
      exponentFourState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commutativeExponentFourMul current
                (exponentFourSeparator z x))
            (exponentFourSeparator z head) =
          exponentFourState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show exponentFourSeparator z z = exponentFourState 1 by
          apply Fin.ext
          simp [exponentFourSeparator, exponentFourState]]
        rw [exponentFourFold_separator]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show exponentFourSeparator z head = exponentFourState 0 by
          apply Fin.ext
          simp [exponentFourSeparator, exponentFourState, hhead]]
        rw [exponentFourFold_separator]
        congr 1
        omega

theorem exponentFourValid_capped_count_eq (e : Identity Nat)
    (valid : e.SatisfiedBy commutativeExponentFour.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 3 =
      min (e.rhs.toList.count z) 3 := by
  intro z
  have evaluated := valid (exponentFourSeparator z)
  rw [exponentFourEval_separator, exponentFourEval_separator] at evaluated
  have valueEq : 3 - min (e.lhs.toList.count z) 3 =
      3 - min (e.rhs.toList.count z) 3 :=
    Fin.mk.inj evaluated
  have lhsBound : min (e.lhs.toList.count z) 3 ≤ 3 :=
    Nat.min_le_right _ _
  have rhsBound : min (e.rhs.toList.count z) 3 ≤ 3 :=
    Nat.min_le_right _ _
  omega

private theorem exponentFourMul_commutative (a b : Fin 4) :
    commutativeExponentFourMul a b =
      commutativeExponentFourMul b a := by
  decide +revert

private theorem exponentFourMul_power (a : Fin 4) :
    commutativeExponentFourMul
        (commutativeExponentFourMul a a) a =
      commutativeExponentFourMul
        (commutativeExponentFourMul
          (commutativeExponentFourMul a a) a) a := by
  decide +revert

theorem commutativeExponentFourBasis_models :
    Models commutativeExponentFour.semigroup
      commutativeExponentFourBasis := by
  intro e he
  simp only [commutativeExponentFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      commutativeExponentFourMul (valuation 0) (valuation 1) =
        commutativeExponentFourMul (valuation 1) (valuation 0)
    exact exponentFourMul_commutative (valuation 0) (valuation 1)
  · intro valuation
    change
      commutativeExponentFourMul
          (commutativeExponentFourMul (valuation 0) (valuation 0))
          (valuation 0) =
        commutativeExponentFourMul
          (commutativeExponentFourMul
            (commutativeExponentFourMul
              (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 0)
    exact exponentFourMul_power (valuation 0)

/-- Unrestricted completeness over `Nat` variables. Every positive exponent
reduces to one, two, or three, and separator valuations distinguish absence
and all three capped positive multiplicities. -/
theorem commutativeExponentFourBasis_complete :
    BasisFor commutativeExponentFour.semigroup
      commutativeExponentFourBasis := by
  refine ⟨commutativeExponentFourBasis_models, ?_⟩
  intro e valid
  have cappedEq := exponentFourValid_capped_count_eq e valid
  have reducedPerm :
      (capThreeReduce e.lhs.toList).Perm
        (capThreeReduce e.rhs.toList) :=
    capThreeReduce_perm_of_capped_count_eq cappedEq
  have lhsNormal := exponentFourDerivesNormal e.lhs
  have rhsNormal := exponentFourDerivesNormal e.rhs
  cases hl : capThreeReduce e.lhs.toList with
  | nil =>
      exact False.elim (exponentFourReduce_cons_ne_nil
        e.lhs.head e.lhs.tail (by simpa [Word.toList] using hl))
  | cons x xs =>
      cases hr : capThreeReduce e.rhs.toList with
      | nil =>
          exact False.elim (exponentFourReduce_cons_ne_nil
            e.rhs.head e.rhs.tail (by simpa [Word.toList] using hr))
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (exponentFourDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

end SemigroupBasis.Examples

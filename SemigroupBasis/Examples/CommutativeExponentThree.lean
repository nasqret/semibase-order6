import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact zero-based form of the table
`[[1,1,1],[1,1,2],[1,2,3]]`. -/
def commutativeExponentThreeMul (a b : Fin 3) : Fin 3 :=
  ⟨a.val + b.val - 2, by omega⟩

/-- The three-element commutative semigroup whose elements record whether a
selected letter occurs zero, one, or at least two times. -/
def commutativeExponentThree : FiniteTable where
  order := 3
  mul := commutativeExponentThreeMul
  assoc := by decide

def exponentX : Word Nat := Word.singleton 0
def exponentXX : Word Nat := ⟨0, [0]⟩
def exponentXXX : Word Nat := ⟨0, [0, 0]⟩
def exponentXY : Word Nat := ⟨0, [1]⟩
def exponentYX : Word Nat := ⟨1, [0]⟩

def exponentThreeLaw : Identity Nat :=
  ⟨exponentXX, exponentXXX⟩

def exponentCommutativityLaw : Identity Nat :=
  ⟨exponentXY, exponentYX⟩

/-- The classical basis `xx = xxx`, `xy = yx`. -/
def commutativeExponentThreeBasis : List (Identity Nat) :=
  [exponentThreeLaw, exponentCommutativityLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem exponentDerivesCommutativity (u v : Word Nat) :
    Derives commutativeExponentThreeBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives commutativeExponentThreeBasis exponentXY exponentYX :=
    Derives.fromBasis (e := exponentCommutativityLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [commutativeExponentThreeBasis, exponentCommutativityLaw,
    exponentXY, exponentYX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton] using h

theorem exponentDerivesTripleContraction (u : Word Nat) :
    Derives commutativeExponentThreeBasis ((u ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives commutativeExponentThreeBasis exponentXXX exponentXX :=
    Derives.symm <|
      Derives.fromBasis (e := exponentThreeLaw) <| by
        exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [commutativeExponentThreeBasis, exponentThreeLaw, exponentXXX,
    exponentXX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives commutativeExponentThreeBasis
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
              exponentDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (exponentDerivesCommutativity
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

theorem exponentDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives commutativeExponentThreeBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain at most two copies of each letter. -/
def exponentReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := exponentReduce xs
      if reduced.count x < 2 then x :: reduced else reduced

theorem count_exponentReduce (z : Nat) (xs : List Nat) :
    (exponentReduce xs).count z = min (xs.count z) 2 := by
  induction xs with
  | nil =>
      simp [exponentReduce]
  | cons x xs ih =>
      simp only [exponentReduce]
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

theorem exponentReduce_count_le_two (z : Nat) (xs : List Nat) :
    (exponentReduce xs).count z ≤ 2 := by
  rw [count_exponentReduce]
  exact Nat.min_le_right _ _

private theorem exponentReduce_cons_ne_nil (x : Nat) (xs : List Nat) :
    exponentReduce (x :: xs) ≠ [] := by
  intro hempty
  have hcount := count_exponentReduce x (x :: xs)
  rw [hempty] at hcount
  simp at hcount
  omega

private theorem two_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 2) :
    xs.Perm (x :: x :: (xs.erase x).erase x) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have herase : (xs.erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hxErase : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans (List.Perm.cons x (List.perm_cons_erase hxErase))

private theorem contractLeadingTriple :
    ∀ x xs,
      Derives commutativeExponentThreeBasis
        (wordOfCons x (x :: x :: xs))
        (wordOfCons x (x :: xs))
  | x, [] => by
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using
          exponentDerivesTripleContraction (Word.singleton x)
  | x, y :: ys => by
      have h :=
        Derives.appendRight
          (exponentDerivesTripleContraction (Word.singleton x))
          (wordOfCons y ys)
      simpa [wordOfCons, Word.append, Word.singleton,
        Word.append_assoc] using h

private theorem exponentDerivesNormalizeList :
    ∀ x xs,
      match exponentReduce (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives commutativeExponentThreeBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := exponentDerivesNormalizeList y ys
      cases hs : exponentReduce (y :: ys) with
      | nil =>
          exact False.elim (exponentReduce_cons_ne_nil y ys hs)
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          by_cases hcount : (z :: zs).count x < 2
          · have reduced :
                exponentReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (exponentReduce (y :: ys)).count x < 2 then
                  x :: exponentReduce (y :: ys)
                else exponentReduce (y :: ys)) = x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have countLe :
                (z :: zs).count x ≤ 2 := by
              rw [← hs]
              exact exponentReduce_count_le_two x (y :: ys)
            have countEq : (z :: zs).count x = 2 := by omega
            let remainder := ((z :: zs).erase x).erase x
            have suffixPerm :
                (z :: zs).Perm (x :: x :: remainder) := by
              simpa [remainder] using
                two_copies_perm x (z :: zs) countEq
            have expandedPerm :
                (x :: z :: zs).Perm (x :: x :: x :: remainder) :=
              List.Perm.cons x suffixPerm
            have arrangedToReduced :
                (x :: x :: remainder).Perm (z :: zs) :=
              suffixPerm.symm
            have arrange :
                Derives commutativeExponentThreeBasis
                  (wordOfCons x (z :: zs))
                  (wordOfCons x (x :: x :: remainder)) :=
              exponentDerivesPermutation _ _ expandedPerm
            have contract :=
              contractLeadingTriple x remainder
            have restore :
                Derives commutativeExponentThreeBasis
                  (wordOfCons x (x :: remainder))
                  (wordOfCons z zs) :=
              exponentDerivesPermutation _ _ arrangedToReduced
            have reduced :
                exponentReduce (x :: y :: ys) = z :: zs := by
              change
                (if (exponentReduce (y :: ys)).count x < 2 then
                  x :: exponentReduce (y :: ys)
                else exponentReduce (y :: ys)) = z :: zs
              rw [hs, if_neg hcount]
            rw [reduced]
            exact Derives.trans
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using prefixed)
              (Derives.trans arrange (Derives.trans contract restore))
termination_by
  _ xs => xs.length

theorem exponentDerivesNormal (w : Word Nat) :
    match exponentReduce w.toList with
    | [] => False
    | x :: xs =>
        Derives commutativeExponentThreeBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact exponentDerivesNormalizeList head tail

theorem exponentReduce_perm_of_capped_count_eq {xs ys : List Nat}
    (hcount : ∀ z, min (xs.count z) 2 = min (ys.count z) 2) :
    (exponentReduce xs).Perm (exponentReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_exponentReduce, count_exponentReduce, hcount z]

private def exponentState (n : Nat) : Fin 3 :=
  ⟨2 - min n 2, by omega⟩

private def exponentSeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 2

private theorem exponentMul_state_one (n : Nat) :
    commutativeExponentThreeMul (exponentState n) 1 =
      exponentState (n + 1) := by
  apply Fin.ext
  simp [commutativeExponentThreeMul, exponentState]
  omega

private theorem exponentMul_state_two (n : Nat) :
    commutativeExponentThreeMul (exponentState n) 2 =
      exponentState n := by
  apply Fin.ext
  simp [commutativeExponentThreeMul, exponentState]

private theorem exponentFold_separator
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          commutativeExponentThreeMul current (exponentSeparator z x))
        (exponentState acc) =
      exponentState (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show exponentSeparator z z = (1 : Fin 3) by
          simp [exponentSeparator]]
        rw [exponentMul_state_one, ih]
        congr 1
        omega
      · rw [List.count_cons_of_ne hx]
        rw [show exponentSeparator z x = (2 : Fin 3) by
          simp [exponentSeparator, hx]]
        rw [exponentMul_state_two, ih]

theorem exponentEval_separator (z : Nat) (w : Word Nat) :
    commutativeExponentThree.semigroup.eval (exponentSeparator z) w =
      exponentState (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              commutativeExponentThreeMul current
                (exponentSeparator z x))
            (exponentSeparator z head) =
          exponentState ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show exponentSeparator z z = exponentState 1 by
          apply Fin.ext
          simp [exponentSeparator, exponentState]]
        rw [exponentFold_separator]
        congr 1
        omega
      · rw [List.count_cons_of_ne hhead]
        rw [show exponentSeparator z head = exponentState 0 by
          apply Fin.ext
          simp [exponentSeparator, exponentState, hhead]]
        rw [exponentFold_separator]
        congr 1
        omega

theorem exponentValid_capped_count_eq (e : Identity Nat)
    (valid : e.SatisfiedBy commutativeExponentThree.semigroup) :
    ∀ z, min (e.lhs.toList.count z) 2 =
      min (e.rhs.toList.count z) 2 := by
  intro z
  have evaluated := valid (exponentSeparator z)
  rw [exponentEval_separator, exponentEval_separator] at evaluated
  have valueEq : 2 - min (e.lhs.toList.count z) 2 =
      2 - min (e.rhs.toList.count z) 2 :=
    Fin.mk.inj evaluated
  have lhsBound : min (e.lhs.toList.count z) 2 ≤ 2 :=
    Nat.min_le_right _ _
  have rhsBound : min (e.rhs.toList.count z) 2 ≤ 2 :=
    Nat.min_le_right _ _
  omega

private theorem exponentMul_power (a : Fin 3) :
    commutativeExponentThreeMul a a =
      commutativeExponentThreeMul
        (commutativeExponentThreeMul a a) a := by
  decide +revert

private theorem exponentMul_commutative (a b : Fin 3) :
    commutativeExponentThreeMul a b =
      commutativeExponentThreeMul b a := by
  decide +revert

theorem commutativeExponentThreeBasis_models :
    Models commutativeExponentThree.semigroup
      commutativeExponentThreeBasis := by
  intro e he
  simp only [commutativeExponentThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      commutativeExponentThreeMul (valuation 0) (valuation 0) =
        commutativeExponentThreeMul
          (commutativeExponentThreeMul (valuation 0) (valuation 0))
          (valuation 0)
    exact exponentMul_power (valuation 0)
  · intro valuation
    change
      commutativeExponentThreeMul (valuation 0) (valuation 1) =
        commutativeExponentThreeMul (valuation 1) (valuation 0)
    exact exponentMul_commutative (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables. Every positive exponent
reduces to one or two, and separator valuations distinguish absence, exponent
one, and exponent at least two for each variable. -/
theorem commutativeExponentThreeBasis_complete :
    BasisFor commutativeExponentThree.semigroup
      commutativeExponentThreeBasis := by
  refine ⟨commutativeExponentThreeBasis_models, ?_⟩
  intro e valid
  have cappedEq := exponentValid_capped_count_eq e valid
  have reducedPerm :
      (exponentReduce e.lhs.toList).Perm
        (exponentReduce e.rhs.toList) :=
    exponentReduce_perm_of_capped_count_eq cappedEq
  have lhsNormal := exponentDerivesNormal e.lhs
  have rhsNormal := exponentDerivesNormal e.rhs
  cases hl : exponentReduce e.lhs.toList with
  | nil =>
      exact False.elim (exponentReduce_cons_ne_nil
        e.lhs.head e.lhs.tail (by simpa [Word.toList] using hl))
  | cons x xs =>
      cases hr : exponentReduce e.rhs.toList with
      | nil =>
          exact False.elim (exponentReduce_cons_ne_nil
            e.rhs.head e.rhs.tail (by simpa [Word.toList] using hr))
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (exponentDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

end SemigroupBasis.Examples

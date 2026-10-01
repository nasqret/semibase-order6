import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Addition modulo three, presented as the exact table
`[[1,2,3],[2,3,1],[3,1,2]]`. -/
def cyclicThreeMul (a b : Fin 3) : Fin 3 :=
  ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩

/-- The cyclic group of order three, viewed as a semigroup. -/
def cyclicThree : FiniteTable where
  order := 3
  mul := cyclicThreeMul
  assoc := by decide

def cyclicThreeX : Word Nat := Word.singleton 0
def cyclicThreeY : Word Nat := Word.singleton 1
def cyclicThreeXY : Word Nat := ⟨0, [1]⟩
def cyclicThreeYX : Word Nat := ⟨1, [0]⟩
def cyclicThreeXXXY : Word Nat := ⟨0, [0, 0, 1]⟩

def cyclicThreeCommutativityLaw : Identity Nat :=
  ⟨cyclicThreeXY, cyclicThreeYX⟩

def cyclicThreeCancellationLaw : Identity Nat :=
  ⟨cyclicThreeXXXY, cyclicThreeY⟩

/-- The semigroup basis `xy = yx`, `xxxy = y` for `C3`. -/
def cyclicThreeBasis : List (Identity Nat) :=
  [cyclicThreeCommutativityLaw, cyclicThreeCancellationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem cyclicThreeDerivesCommutativity (u v : Word Nat) :
    Derives cyclicThreeBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicThreeBasis cyclicThreeXY cyclicThreeYX :=
    Derives.fromBasis (e := cyclicThreeCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [cyclicThreeBasis, cyclicThreeCommutativityLaw,
    cyclicThreeXY, cyclicThreeYX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton] using h

theorem cyclicThreeDerivesCancelCube (u v : Word Nat) :
    Derives cyclicThreeBasis (((u ++ u) ++ u) ++ v) v := by
  have hbase :
      Derives cyclicThreeBasis cyclicThreeXXXY cyclicThreeY :=
    Derives.fromBasis (e := cyclicThreeCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [cyclicThreeBasis, cyclicThreeCancellationLaw,
    cyclicThreeXXXY, cyclicThreeY, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Every cube represents the unique nonempty zero exponent vector. -/
theorem cyclicThreeDerivesCommonCube (u v : Word Nat) :
    Derives cyclicThreeBasis ((u ++ u) ++ u) ((v ++ v) ++ v) := by
  have addV :
      Derives cyclicThreeBasis ((u ++ u) ++ u)
        (((v ++ v) ++ v) ++ ((u ++ u) ++ u)) :=
    Derives.symm
      (cyclicThreeDerivesCancelCube v ((u ++ u) ++ u))
  have commute :
      Derives cyclicThreeBasis
        (((v ++ v) ++ v) ++ ((u ++ u) ++ u))
        (((u ++ u) ++ u) ++ ((v ++ v) ++ v)) :=
    cyclicThreeDerivesCommutativity
      ((v ++ v) ++ v) ((u ++ u) ++ u)
  exact Derives.trans addV <|
    Derives.trans commute
      (cyclicThreeDerivesCancelCube u ((v ++ v) ++ v))

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicThreeBasis
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
              cyclicThreeDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicThreeDerivesCommutativity
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

theorem cyclicThreeDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicThreeBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain zero, one, or two copies according to multiplicity modulo three. -/
def ternaryReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := ternaryReduce xs
      if reduced.count x < 2 then x :: reduced
      else (reduced.erase x).erase x

theorem count_ternaryReduce (z : Nat) (xs : List Nat) :
    (ternaryReduce xs).count z = xs.count z % 3 := by
  induction xs generalizing z with
  | nil =>
      simp [ternaryReduce]
  | cons x xs ih =>
      simp only [ternaryReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · have reducedLe :
            (ternaryReduce xs).count x < 3 := by
          rw [ih x]
          exact Nat.mod_lt _ (by decide)
        have reducedEq : (ternaryReduce xs).count x = 2 := by
          omega
        by_cases hzx : z = x
        · subst z
          have countMod : xs.count x % 3 = 2 := by
            rw [← ih x]
            exact reducedEq
          rw [List.count_erase_self, List.count_erase_self,
            List.count_cons_self, reducedEq]
          simp [Nat.add_mod, countMod]
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx), ih]

theorem ternaryReduce_perm_of_mod_eq {xs ys : List Nat}
    (hmod : ∀ z, xs.count z % 3 = ys.count z % 3) :
    (ternaryReduce xs).Perm (ternaryReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_ternaryReduce, count_ternaryReduce, hmod z]

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

private theorem cyclicThreeDerivesNormalizeList :
    ∀ x xs,
      match ternaryReduce (x :: xs) with
      | [] =>
          Derives cyclicThreeBasis (wordOfCons x xs)
            ((Word.singleton x ++ Word.singleton x) ++ Word.singleton x)
      | y :: ys =>
          Derives cyclicThreeBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := cyclicThreeDerivesNormalizeList y ys
      cases hs : ternaryReduce (y :: ys) with
      | nil =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have commute :=
            cyclicThreeDerivesCommutativity
              (Word.singleton x)
              ((Word.singleton y ++ Word.singleton y) ++
                Word.singleton y)
          have cancel :=
            cyclicThreeDerivesCancelCube
              (Word.singleton y) (Word.singleton x)
          have reduced : ternaryReduce (x :: y :: ys) = [x] := by
            change
              (if (ternaryReduce (y :: ys)).count x < 2 then
                x :: ternaryReduce (y :: ys)
              else
                ((ternaryReduce (y :: ys)).erase x).erase x) = [x]
            rw [hs]
            rfl
          rw [reduced]
          exact Derives.trans
            (by
              simpa [wordOfCons, Word.append, Word.singleton,
                Word.append_assoc] using prefixed)
            (Derives.trans
              (by simpa [Word.append_assoc] using commute)
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using cancel))
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          let normal : Word Nat := wordOfCons z zs
          by_cases hcount : (z :: zs).count x < 2
          · have reduced :
                ternaryReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (ternaryReduce (y :: ys)).count x < 2 then
                  x :: ternaryReduce (y :: ys)
                else
                  ((ternaryReduce (y :: ys)).erase x).erase x) =
                    x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [normal, wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have reducedLe :
                (z :: zs).count x < 3 := by
              have h := count_ternaryReduce x (y :: ys)
              rw [hs] at h
              rw [h]
              exact Nat.mod_lt _ (by decide)
            have countEq : (z :: zs).count x = 2 := by
              omega
            have hperm :=
              two_copies_perm x (z :: zs) countEq
            have reorder :
                Derives cyclicThreeBasis normal
                  (wordOfCons x
                    (x :: ((z :: zs).erase x).erase x)) :=
              cyclicThreeDerivesPermutation normal
                (wordOfCons x
                  (x :: ((z :: zs).erase x).erase x)) hperm
            have withPrefix :=
              Derives.prepend (Word.singleton x) reorder
            cases he : ((z :: zs).erase x).erase x with
            | nil =>
                have reduced :
                    ternaryReduce (x :: y :: ys) = [] := by
                  change
                    (if (ternaryReduce (y :: ys)).count x < 2 then
                      x :: ternaryReduce (y :: ys)
                    else
                      ((ternaryReduce (y :: ys)).erase x).erase x) = []
                  rw [hs, if_neg hcount, he]
                rw [he] at withPrefix
                rw [reduced]
                exact Derives.trans
                  (by
                    simpa [normal, wordOfCons, Word.append,
                      Word.singleton, Word.append_assoc] using prefixed)
                  (by
                    simpa [normal, wordOfCons, Word.append,
                      Word.singleton, Word.append_assoc] using withPrefix)
            | cons r rs =>
                let remainder : Word Nat := wordOfCons r rs
                have cancel :=
                  cyclicThreeDerivesCancelCube
                    (Word.singleton x) remainder
                have reduced :
                    ternaryReduce (x :: y :: ys) = r :: rs := by
                  change
                    (if (ternaryReduce (y :: ys)).count x < 2 then
                      x :: ternaryReduce (y :: ys)
                    else
                      ((ternaryReduce (y :: ys)).erase x).erase x) =
                        r :: rs
                  rw [hs, if_neg hcount, he]
                rw [he] at withPrefix
                rw [reduced]
                exact Derives.trans
                  (by
                    simpa [normal, wordOfCons, Word.append,
                      Word.singleton, Word.append_assoc] using prefixed)
                  (Derives.trans
                    (by
                      simpa [normal, remainder, wordOfCons, Word.append,
                        Word.singleton, Word.append_assoc] using withPrefix)
                    (by
                      simpa [remainder, wordOfCons, Word.append,
                        Word.singleton, Word.append_assoc] using cancel))
termination_by
  _ xs => xs.length

theorem cyclicThreeDerivesNormal (w : Word Nat) :
    match ternaryReduce w.toList with
    | [] =>
        Derives cyclicThreeBasis w
          ((Word.singleton w.head ++ Word.singleton w.head) ++
            Word.singleton w.head)
    | x :: xs =>
        Derives cyclicThreeBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact cyclicThreeDerivesNormalizeList head tail

private def ternaryValue (n : Nat) : Fin 3 :=
  ⟨n % 3, Nat.mod_lt _ (by decide)⟩

private theorem cyclicThreeMul_ternaryValue (m n : Nat) :
    cyclicThreeMul (ternaryValue m) (ternaryValue n) =
      ternaryValue (m + n) := by
  apply Fin.ext
  simp [cyclicThreeMul, ternaryValue, Nat.add_mod]

private def ternarySeparator (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 0

private theorem cyclicThreeFold_separator
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          cyclicThreeMul current (ternarySeparator z x))
        (ternaryValue acc) =
      ternaryValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show ternarySeparator z z = ternaryValue 1 by
          simp [ternarySeparator, ternaryValue]]
        rw [cyclicThreeMul_ternaryValue, ih]
        apply Fin.ext
        simp [ternaryValue, Nat.add_comm, Nat.add_left_comm]
      · rw [List.count_cons_of_ne hx]
        rw [show ternarySeparator z x = ternaryValue 0 by
          simp [ternarySeparator, hx, ternaryValue]]
        rw [cyclicThreeMul_ternaryValue, ih]
        apply Fin.ext
        simp [ternaryValue]

theorem cyclicThreeEval_separator (z : Nat) (w : Word Nat) :
    cyclicThree.semigroup.eval (ternarySeparator z) w =
      ternaryValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicThreeMul current (ternarySeparator z x))
            (ternarySeparator z head) =
          ternaryValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show ternarySeparator z z = ternaryValue 1 by
          simp [ternarySeparator, ternaryValue]]
        rw [cyclicThreeFold_separator]
        apply Fin.ext
        simp [ternaryValue, Nat.add_comm]
      · rw [List.count_cons_of_ne hhead]
        rw [show ternarySeparator z head = ternaryValue 0 by
          simp [ternarySeparator, hhead, ternaryValue]]
        rw [cyclicThreeFold_separator]
        apply Fin.ext
        simp [ternaryValue]

theorem cyclicThreeValid_mod_eq (e : Identity Nat)
    (valid : e.SatisfiedBy cyclicThree.semigroup) :
    ∀ z, e.lhs.toList.count z % 3 =
      e.rhs.toList.count z % 3 := by
  intro z
  have evaluated := valid (ternarySeparator z)
  rw [cyclicThreeEval_separator, cyclicThreeEval_separator] at evaluated
  exact Fin.mk.inj evaluated

theorem cyclicThreeBasis_models :
    Models cyclicThree.semigroup cyclicThreeBasis := by
  intro e he
  simp only [cyclicThreeBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change cyclicThreeMul (valuation 0) (valuation 1) =
      cyclicThreeMul (valuation 1) (valuation 0)
    apply Fin.ext
    simp [cyclicThreeMul, Nat.add_comm]
  · intro valuation
    change
      cyclicThreeMul
          (cyclicThreeMul
            (cyclicThreeMul (valuation 0) (valuation 0))
            (valuation 0))
          (valuation 1) =
        valuation 1
    have cancellation (a b : Fin 3) :
        cyclicThreeMul
            (cyclicThreeMul (cyclicThreeMul a a) a) b = b := by
      decide +revert
    exact cancellation (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables. Equal exponent vectors
modulo three normalize to the same one-or-two-copy support; the zero vector
uses the common cube class. -/
theorem cyclicThreeBasis_complete :
    BasisFor cyclicThree.semigroup cyclicThreeBasis := by
  refine ⟨cyclicThreeBasis_models, ?_⟩
  intro e valid
  have modEq := cyclicThreeValid_mod_eq e valid
  have reducedPerm :
      (ternaryReduce e.lhs.toList).Perm
        (ternaryReduce e.rhs.toList) :=
    ternaryReduce_perm_of_mod_eq modEq
  have lhsNormal := cyclicThreeDerivesNormal e.lhs
  have rhsNormal := cyclicThreeDerivesNormal e.rhs
  cases hl : ternaryReduce e.lhs.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : ternaryReduce e.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicThreeDerivesCommonCube
            (Word.singleton e.lhs.head)
            (Word.singleton e.rhs.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : ternaryReduce e.rhs.toList with
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

theorem cyclicThree_selfDual :
    cyclicThree.semigroup.opposite = cyclicThree.semigroup := by
  unfold cyclicThree FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  simp [cyclicThreeMul, Nat.add_comm]

theorem cyclicThreeOppositeBasis_complete :
    BasisFor cyclicThree.semigroup.opposite cyclicThreeBasis := by
  rw [cyclicThree_selfDual]
  exact cyclicThreeBasis_complete

end SemigroupBasis.Examples

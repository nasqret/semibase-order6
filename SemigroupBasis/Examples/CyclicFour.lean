import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Addition modulo four, presented as the exact cyclic group table. -/
def cyclicFourMul (a b : Fin 4) : Fin 4 :=
  ⟨(a.val + b.val) % 4, Nat.mod_lt _ (by decide)⟩

/-- The cyclic group of order four, viewed as a semigroup. -/
def cyclicFour : FiniteTable where
  order := 4
  mul := cyclicFourMul
  assoc := by decide

def cyclicFourX : Word Nat := Word.singleton 0
def cyclicFourY : Word Nat := Word.singleton 1
def cyclicFourXY : Word Nat := ⟨0, [1]⟩
def cyclicFourYX : Word Nat := ⟨1, [0]⟩
def cyclicFourXXXXY : Word Nat := ⟨0, [0, 0, 0, 1]⟩

def cyclicFourCommutativityLaw : Identity Nat :=
  ⟨cyclicFourXY, cyclicFourYX⟩

def cyclicFourCancellationLaw : Identity Nat :=
  ⟨cyclicFourXXXXY, cyclicFourY⟩

/-- The semigroup basis `xy = yx`, `xxxxy = y` for `C4`. -/
def cyclicFourBasis : List (Identity Nat) :=
  [cyclicFourCommutativityLaw, cyclicFourCancellationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem cyclicFourDerivesCommutativity (u v : Word Nat) :
    Derives cyclicFourBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicFourBasis cyclicFourXY cyclicFourYX :=
    Derives.fromBasis (e := cyclicFourCommutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [cyclicFourBasis, cyclicFourCommutativityLaw,
    cyclicFourXY, cyclicFourYX, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton] using h

theorem cyclicFourDerivesCancelFourth (u v : Word Nat) :
    Derives cyclicFourBasis
      ((((u ++ u) ++ u) ++ u) ++ v) v := by
  have hbase :
      Derives cyclicFourBasis cyclicFourXXXXY cyclicFourY :=
    Derives.fromBasis (e := cyclicFourCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [cyclicFourBasis, cyclicFourCancellationLaw,
    cyclicFourXXXXY, cyclicFourY, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton, Word.append_assoc] using h

/-- Every fourth power represents the unique nonempty zero exponent vector. -/
theorem cyclicFourDerivesCommonFourth (u v : Word Nat) :
    Derives cyclicFourBasis
      (((u ++ u) ++ u) ++ u) (((v ++ v) ++ v) ++ v) := by
  have addV :
      Derives cyclicFourBasis
        (((u ++ u) ++ u) ++ u)
        ((((v ++ v) ++ v) ++ v) ++ (((u ++ u) ++ u) ++ u)) :=
    Derives.symm
      (cyclicFourDerivesCancelFourth v (((u ++ u) ++ u) ++ u))
  have commute :
      Derives cyclicFourBasis
        ((((v ++ v) ++ v) ++ v) ++ (((u ++ u) ++ u) ++ u))
        ((((u ++ u) ++ u) ++ u) ++ (((v ++ v) ++ v) ++ v)) :=
    cyclicFourDerivesCommutativity
      (((v ++ v) ++ v) ++ v) (((u ++ u) ++ u) ++ u)
  exact Derives.trans addV <|
    Derives.trans commute
      (cyclicFourDerivesCancelFourth u (((v ++ v) ++ v) ++ v))

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicFourBasis
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
              cyclicFourDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicFourDerivesCommutativity
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

theorem cyclicFourDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicFourBasis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain zero, one, two, or three copies according to multiplicity modulo
four. -/
def quaternaryReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := quaternaryReduce xs
      if reduced.count x < 3 then x :: reduced
      else ((reduced.erase x).erase x).erase x

theorem count_quaternaryReduce (z : Nat) (xs : List Nat) :
    (quaternaryReduce xs).count z = xs.count z % 4 := by
  induction xs generalizing z with
  | nil =>
      simp [quaternaryReduce]
  | cons x xs ih =>
      simp only [quaternaryReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · have reducedLe :
            (quaternaryReduce xs).count x < 4 := by
          rw [ih x]
          exact Nat.mod_lt _ (by decide)
        have reducedEq : (quaternaryReduce xs).count x = 3 := by
          omega
        by_cases hzx : z = x
        · subst z
          have countMod : xs.count x % 4 = 3 := by
            rw [← ih x]
            exact reducedEq
          rw [List.count_erase_self, List.count_erase_self,
            List.count_erase_self, List.count_cons_self, reducedEq]
          simp [Nat.add_mod, countMod]
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx), ih]

theorem quaternaryReduce_perm_of_mod_eq {xs ys : List Nat}
    (hmod : ∀ z, xs.count z % 4 = ys.count z % 4) :
    (quaternaryReduce xs).Perm (quaternaryReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_quaternaryReduce, count_quaternaryReduce, hmod z]

private theorem three_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 3) :
    xs.Perm
      (x :: x :: x :: ((xs.erase x).erase x).erase x) := by
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

private theorem cyclicFourDerivesNormalizeList :
    ∀ x xs,
      match quaternaryReduce (x :: xs) with
      | [] =>
          Derives cyclicFourBasis (wordOfCons x xs)
            (((Word.singleton x ++ Word.singleton x) ++
                Word.singleton x) ++ Word.singleton x)
      | y :: ys =>
          Derives cyclicFourBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := cyclicFourDerivesNormalizeList y ys
      cases hs : quaternaryReduce (y :: ys) with
      | nil =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have commute :=
            cyclicFourDerivesCommutativity
              (Word.singleton x)
              (((Word.singleton y ++ Word.singleton y) ++
                  Word.singleton y) ++ Word.singleton y)
          have cancel :=
            cyclicFourDerivesCancelFourth
              (Word.singleton y) (Word.singleton x)
          have reduced : quaternaryReduce (x :: y :: ys) = [x] := by
            change
              (if (quaternaryReduce (y :: ys)).count x < 3 then
                x :: quaternaryReduce (y :: ys)
              else
                (((quaternaryReduce (y :: ys)).erase x).erase x).erase x) =
                [x]
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
          by_cases hcount : (z :: zs).count x < 3
          · have reduced :
                quaternaryReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (quaternaryReduce (y :: ys)).count x < 3 then
                  x :: quaternaryReduce (y :: ys)
                else
                  (((quaternaryReduce (y :: ys)).erase x).erase x).erase x) =
                    x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [normal, wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have reducedLe :
                (z :: zs).count x < 4 := by
              have h := count_quaternaryReduce x (y :: ys)
              rw [hs] at h
              rw [h]
              exact Nat.mod_lt _ (by decide)
            have countEq : (z :: zs).count x = 3 := by
              omega
            have hperm :=
              three_copies_perm x (z :: zs) countEq
            have reorder :
                Derives cyclicFourBasis normal
                  (wordOfCons x
                    (x :: x :: (((z :: zs).erase x).erase x).erase x)) :=
              cyclicFourDerivesPermutation normal
                (wordOfCons x
                  (x :: x :: (((z :: zs).erase x).erase x).erase x))
                hperm
            have withPrefix :=
              Derives.prepend (Word.singleton x) reorder
            cases he : (((z :: zs).erase x).erase x).erase x with
            | nil =>
                have reduced :
                    quaternaryReduce (x :: y :: ys) = [] := by
                  change
                    (if (quaternaryReduce (y :: ys)).count x < 3 then
                      x :: quaternaryReduce (y :: ys)
                    else
                      (((quaternaryReduce (y :: ys)).erase x).erase x).erase x) =
                      []
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
                  cyclicFourDerivesCancelFourth
                    (Word.singleton x) remainder
                have reduced :
                    quaternaryReduce (x :: y :: ys) = r :: rs := by
                  change
                    (if (quaternaryReduce (y :: ys)).count x < 3 then
                      x :: quaternaryReduce (y :: ys)
                    else
                      (((quaternaryReduce (y :: ys)).erase x).erase x).erase x) =
                        r :: rs
                  rw [hs, if_neg hcount, he]
                rw [he] at withPrefix
                rw [reduced]
                exact Derives.trans
                  (by
                    simpa [normal, wordOfCons, Word.append, Word.singleton,
                      Word.append_assoc] using prefixed)
                  (Derives.trans
                    (by
                      simpa [normal, remainder, wordOfCons, Word.append,
                        Word.singleton, Word.append_assoc] using withPrefix)
                    (by
                      simpa [remainder, wordOfCons, Word.append,
                        Word.singleton, Word.append_assoc] using cancel))
termination_by
  _ xs => xs.length

theorem cyclicFourDerivesNormal (w : Word Nat) :
    match quaternaryReduce w.toList with
    | [] =>
        Derives cyclicFourBasis w
          (((Word.singleton w.head ++ Word.singleton w.head) ++
              Word.singleton w.head) ++ Word.singleton w.head)
    | x :: xs =>
        Derives cyclicFourBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact cyclicFourDerivesNormalizeList head tail

private def quaternaryValue (n : Nat) : Fin 4 :=
  ⟨n % 4, Nat.mod_lt _ (by decide)⟩

private theorem cyclicFourMul_quaternaryValue (m n : Nat) :
    cyclicFourMul (quaternaryValue m) (quaternaryValue n) =
      quaternaryValue (m + n) := by
  apply Fin.ext
  simp [cyclicFourMul, quaternaryValue, Nat.add_mod]

private def quaternarySeparator (z : Nat) : Nat → Fin 4 :=
  fun x => if x = z then 1 else 0

private theorem cyclicFourFold_separator
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          cyclicFourMul current (quaternarySeparator z x))
        (quaternaryValue acc) =
      quaternaryValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show quaternarySeparator z z = quaternaryValue 1 by
          simp [quaternarySeparator, quaternaryValue]]
        rw [cyclicFourMul_quaternaryValue, ih]
        apply Fin.ext
        simp [quaternaryValue, Nat.add_comm, Nat.add_left_comm]
      · rw [List.count_cons_of_ne hx]
        rw [show quaternarySeparator z x = quaternaryValue 0 by
          simp [quaternarySeparator, hx, quaternaryValue]]
        rw [cyclicFourMul_quaternaryValue, ih]
        apply Fin.ext
        simp [quaternaryValue]

theorem cyclicFourEval_separator (z : Nat) (w : Word Nat) :
    cyclicFour.semigroup.eval (quaternarySeparator z) w =
      quaternaryValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicFourMul current (quaternarySeparator z x))
            (quaternarySeparator z head) =
          quaternaryValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show quaternarySeparator z z = quaternaryValue 1 by
          simp [quaternarySeparator, quaternaryValue]]
        rw [cyclicFourFold_separator]
        apply Fin.ext
        simp [quaternaryValue, Nat.add_comm]
      · rw [List.count_cons_of_ne hhead]
        rw [show quaternarySeparator z head = quaternaryValue 0 by
          simp [quaternarySeparator, hhead, quaternaryValue]]
        rw [cyclicFourFold_separator]
        apply Fin.ext
        simp [quaternaryValue]

theorem cyclicFourValid_mod_eq (e : Identity Nat)
    (valid : e.SatisfiedBy cyclicFour.semigroup) :
    ∀ z, e.lhs.toList.count z % 4 =
      e.rhs.toList.count z % 4 := by
  intro z
  have evaluated := valid (quaternarySeparator z)
  rw [cyclicFourEval_separator, cyclicFourEval_separator] at evaluated
  exact Fin.mk.inj evaluated

theorem cyclicFourBasis_models :
    Models cyclicFour.semigroup cyclicFourBasis := by
  intro e he
  simp only [cyclicFourBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change cyclicFourMul (valuation 0) (valuation 1) =
      cyclicFourMul (valuation 1) (valuation 0)
    apply Fin.ext
    simp [cyclicFourMul, Nat.add_comm]
  · intro valuation
    change
      cyclicFourMul
          (cyclicFourMul
            (cyclicFourMul
              (cyclicFourMul (valuation 0) (valuation 0))
              (valuation 0))
            (valuation 0))
          (valuation 1) =
        valuation 1
    have cancellation (a b : Fin 4) :
        cyclicFourMul
            (cyclicFourMul
              (cyclicFourMul (cyclicFourMul a a) a) a) b = b := by
      decide +revert
    exact cancellation (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables. Equal exponent vectors
modulo four normalize to the same one-to-three-copy support; the zero vector
uses the common fourth-power class. -/
theorem cyclicFourBasis_complete :
    BasisFor cyclicFour.semigroup cyclicFourBasis := by
  refine ⟨cyclicFourBasis_models, ?_⟩
  intro e valid
  have modEq := cyclicFourValid_mod_eq e valid
  have reducedPerm :
      (quaternaryReduce e.lhs.toList).Perm
        (quaternaryReduce e.rhs.toList) :=
    quaternaryReduce_perm_of_mod_eq modEq
  have lhsNormal := cyclicFourDerivesNormal e.lhs
  have rhsNormal := cyclicFourDerivesNormal e.rhs
  cases hl : quaternaryReduce e.lhs.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : quaternaryReduce e.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicFourDerivesCommonFourth
            (Word.singleton e.lhs.head)
            (Word.singleton e.rhs.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : quaternaryReduce e.rhs.toList with
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

theorem cyclicFour_selfDual :
    cyclicFour.semigroup.opposite = cyclicFour.semigroup := by
  unfold cyclicFour FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext a b
  apply Fin.ext
  simp [cyclicFourMul, Nat.add_comm]

theorem cyclicFourOppositeBasis_complete :
    BasisFor cyclicFour.semigroup.opposite cyclicFourBasis := by
  rw [cyclicFour_selfDual]
  exact cyclicFourBasis_complete

end SemigroupBasis.Examples

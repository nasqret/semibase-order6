import SemigroupBasis.Examples.CyclicFive
import SemigroupBasis.FiniteReflection

/-!
# The unrestricted semigroup identity basis of the cyclic group C6

This module binds the exact Smallsemi table `S6_14996` and proves that
`xy = yx`, `yx^6 = y` is a complete semigroup identity basis.  The
completeness proof was proposed by Harmonic Aristotle and is retained here
only after repository review and fresh WMI compilation.
-/

namespace SemigroupBasis.CoRoots.Order6CyclicSix

open SemigroupBasis

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based Smallsemi table `S6_14996`, the cyclic group C6. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 2 3 4 5 right else
    if left = 1 then row6 1 0 5 4 3 2 right else
      if left = 2 then row6 2 5 3 0 1 4 right else
        if left = 3 then row6 3 4 0 2 5 1 right else
          if left = 4 then row6 4 3 1 5 2 0 right else
            row6 5 2 4 1 0 3 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (table.semigroup.mul left right).val + 1

theorem tableOneBased_certificate :
    tableOneBased =
      [[1, 2, 3, 4, 5, 6],
       [2, 1, 6, 5, 4, 3],
       [3, 6, 4, 1, 2, 5],
       [4, 5, 1, 3, 6, 2],
       [5, 4, 2, 6, 3, 1],
       [6, 3, 5, 2, 1, 4]] := by
  decide

def x : Word Nat := Word.singleton 0
def y : Word Nat := Word.singleton 1
def xy : Word Nat := ⟨0, [1]⟩
def yx : Word Nat := ⟨1, [0]⟩
def yxxxxxx : Word Nat := ⟨1, [0, 0, 0, 0, 0, 0]⟩

def commutativityLaw : Identity Nat := ⟨xy, yx⟩
def cancellationLaw : Identity Nat := ⟨yxxxxxx, y⟩

/-- The classical two-identity semigroup basis `xy = yx`, `yx^6 = y` for C6. -/
def basis : List (Identity Nat) :=
  [commutativityLaw, cancellationLaw]

def finiteCommutativityLaw : Identity (Fin 2) :=
  ⟨⟨0, [1]⟩, ⟨1, [0]⟩⟩

def finiteCancellationLaw : Identity (Fin 2) :=
  ⟨⟨1, [0, 0, 0, 0, 0, 0]⟩, ⟨1, []⟩⟩

theorem finiteCommutativityLaw_map :
    finiteCommutativityLaw.map Fin.val = commutativityLaw := rfl

theorem finiteCancellationLaw_map :
    finiteCancellationLaw.map Fin.val = cancellationLaw := rfl

theorem basis_models : Models table.semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [← finiteCommutativityLaw_map]
    exact table.checkIdentityNat_sound finiteCommutativityLaw (by decide)
  · rw [← finiteCancellationLaw_map]
    exact table.checkIdentityNat_sound finiteCancellationLaw (by decide)

private def cyclicSixEncode (a : Fin 6) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 5 else if a = 2 then 3 else
  if a = 3 then 1 else if a = 4 then 2 else 4

private def cyclicSixDecode (a : Fin 6) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 3 else if a = 2 then 4 else
  if a = 3 then 2 else if a = 4 then 5 else 1

private theorem cyclicSixDecode_encode (a : Fin 6) :
    cyclicSixDecode (cyclicSixEncode a) = a := by
  decide +revert

private def cyclicSixMul (a b : Fin 6) : Fin 6 := mul a b

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem cyclicSixDerivesCommutativity (u v : Word Nat) :
    Derives basis (u ++ v) (v ++ u) := by
  have hbase :
      Derives basis xy yx :=
    Derives.fromBasis (e := commutativityLaw) <|
      List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [basis, commutativityLaw,
    xy, yx, instantiateTwoWords, Word.bind,
    Word.append, Word.singleton] using h

theorem cyclicSixDerivesCancelSixth (u v : Word Nat) :
    Derives basis
      ((((((u ++ u) ++ u) ++ u) ++ u) ++ u) ++ v) v := by
  have hbase : Derives basis yxxxxxx y :=
    Derives.fromBasis (e := cancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have hsub := Derives.subst hbase (instantiateTwoWords u v)
  have hcomm := cyclicSixDerivesCommutativity
    (((((u ++ u) ++ u) ++ u) ++ u) ++ u) v
  exact Derives.trans hcomm (by
    simpa [basis, cancellationLaw, yxxxxxx, y, instantiateTwoWords,
      Word.bind, Word.append, Word.singleton, Word.append_assoc] using hsub)

/-- Every sixth power represents the unique nonempty zero exponent vector. -/
theorem cyclicSixDerivesCommonSixth (u v : Word Nat) :
    Derives basis
      (((((u ++ u) ++ u) ++ u) ++ u) ++ u)
      (((((v ++ v) ++ v) ++ v) ++ v) ++ v) := by
  have addV :
      Derives basis
        (((((u ++ u) ++ u) ++ u) ++ u) ++ u)
        ((((((v ++ v) ++ v) ++ v) ++ v) ++ v) ++
          (((((u ++ u) ++ u) ++ u) ++ u) ++ u)) :=
    Derives.symm
      (cyclicSixDerivesCancelSixth v
        (((((u ++ u) ++ u) ++ u) ++ u) ++ u))
  have commute :
      Derives basis
        ((((((v ++ v) ++ v) ++ v) ++ v) ++ v) ++
          (((((u ++ u) ++ u) ++ u) ++ u) ++ u))
        ((((((u ++ u) ++ u) ++ u) ++ u) ++ u) ++
          (((((v ++ v) ++ v) ++ v) ++ v) ++ v)) :=
    cyclicSixDerivesCommutativity
      (((((v ++ v) ++ v) ++ v) ++ v) ++ v)
      (((((u ++ u) ++ u) ++ u) ++ u) ++ u)
  exact Derives.trans addV <|
    Derives.trans commute
      (cyclicSixDerivesCancelSixth u
        (((((v ++ v) ++ v) ++ v) ++ v) ++ v))

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives basis
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
              cyclicSixDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicSixDerivesCommutativity
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

theorem cyclicSixDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives basis u v := by
  cases u with
  | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Retain zero through five copies according to multiplicity modulo six. -/
def senaryReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := senaryReduce xs
      if reduced.count x < 5 then x :: reduced
      else ((((reduced.erase x).erase x).erase x).erase x).erase x

theorem count_senaryReduce (z : Nat) (xs : List Nat) :
    (senaryReduce xs).count z = xs.count z % 6 := by
  induction xs generalizing z with
  | nil =>
      simp [senaryReduce]
  | cons x xs ih =>
      simp only [senaryReduce]
      split <;> rename_i hcount
      · by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self, List.count_cons_self, ih]
          rw [ih] at hcount
          omega
        · rw [List.count_cons_of_ne (Ne.symm hzx),
            List.count_cons_of_ne (Ne.symm hzx), ih]
      · have reducedLe :
            (senaryReduce xs).count x < 6 := by
          rw [ih x]
          exact Nat.mod_lt _ (by decide)
        have reducedEq : (senaryReduce xs).count x = 5 := by
          omega
        by_cases hzx : z = x
        · subst z
          have countMod : xs.count x % 6 = 5 := by
            rw [← ih x]
            exact reducedEq
          rw [List.count_erase_self, List.count_erase_self,
            List.count_erase_self, List.count_erase_self, List.count_erase_self,
            List.count_cons_self, reducedEq]
          simp [Nat.add_mod, countMod]
        · rw [List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx,
            List.count_erase_of_ne hzx, List.count_erase_of_ne hzx,
            List.count_cons_of_ne (Ne.symm hzx), ih]

theorem senaryReduce_perm_of_mod_eq {xs ys : List Nat}
    (hmod : ∀ z, xs.count z % 6 = ys.count z % 6) :
    (senaryReduce xs).Perm (senaryReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  rw [count_senaryReduce, count_senaryReduce, hmod z]

private theorem six_copies_perm (x : Nat) (xs : List Nat)
    (hcount : xs.count x = 5) :
    xs.Perm
      (x :: x :: x :: x :: x ::
        (((((xs.erase x).erase x).erase x).erase x).erase x)) := by
  have hx : x ∈ xs := List.count_pos_iff.mp (by omega)
  have first := List.perm_cons_erase hx
  have hcount₁ : (xs.erase x).count x = 4 := by
    rw [List.count_erase_self]
    omega
  have hx₁ : x ∈ xs.erase x :=
    List.count_pos_iff.mp (by omega)
  have second := List.perm_cons_erase hx₁
  have hcount₂ : ((xs.erase x).erase x).count x = 3 := by
    rw [List.count_erase_self]
    omega
  have hx₂ : x ∈ (xs.erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have third := List.perm_cons_erase hx₂
  have hcount₃ : (((xs.erase x).erase x).erase x).count x = 2 := by
    rw [List.count_erase_self]
    omega
  have hx₃ : x ∈ ((xs.erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  have fourth := List.perm_cons_erase hx₃
  have hcount₄ : ((((xs.erase x).erase x).erase x).erase x).count x = 1 := by
    rw [List.count_erase_self]
    omega
  have hx₄ : x ∈ (((xs.erase x).erase x).erase x).erase x :=
    List.count_pos_iff.mp (by omega)
  exact first.trans <| List.Perm.cons x <|
    second.trans <| List.Perm.cons x <|
      third.trans <| List.Perm.cons x <|
        fourth.trans <| List.Perm.cons x (List.perm_cons_erase hx₄)

private theorem cyclicSixDerivesNormalizeList :
    ∀ x xs,
      match senaryReduce (x :: xs) with
      | [] =>
          Derives basis (wordOfCons x xs)
            (((((Word.singleton x ++ Word.singleton x) ++
                Word.singleton x) ++ Word.singleton x) ++
              Word.singleton x) ++ Word.singleton x)
      | y :: ys =>
          Derives basis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := cyclicSixDerivesNormalizeList y ys
      cases hs : senaryReduce (y :: ys) with
      | nil =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have commute :=
            cyclicSixDerivesCommutativity
              (Word.singleton x)
              (((((Word.singleton y ++ Word.singleton y) ++
                  Word.singleton y) ++ Word.singleton y) ++
                Word.singleton y) ++ Word.singleton y)
          have cancel :=
            cyclicSixDerivesCancelSixth
              (Word.singleton y) (Word.singleton x)
          have reduced : senaryReduce (x :: y :: ys) = [x] := by
            change
              (if (senaryReduce (y :: ys)).count x < 5 then
                x :: senaryReduce (y :: ys)
              else
                (((((senaryReduce (y :: ys)).erase x).erase x).erase x).erase x).erase x) =
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
          by_cases hcount : (z :: zs).count x < 5
          · have reduced :
                senaryReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if (senaryReduce (y :: ys)).count x < 5 then
                  x :: senaryReduce (y :: ys)
                else
                  (((((senaryReduce (y :: ys)).erase x).erase x).erase x).erase x).erase x) =
                    x :: z :: zs
              rw [hs, if_pos hcount]
            rw [reduced]
            simpa [normal, wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
          · have reducedLe :
                (z :: zs).count x < 6 := by
              have h := count_senaryReduce x (y :: ys)
              rw [hs] at h
              rw [h]
              exact Nat.mod_lt _ (by decide)
            have countEq : (z :: zs).count x = 5 := by
              omega
            have hperm :=
              six_copies_perm x (z :: zs) countEq
            have reorder :
                Derives basis normal
                  (wordOfCons x
                    (x :: x :: x :: x ::
                      (((((z :: zs).erase x).erase x).erase x).erase x).erase x)) :=
              cyclicSixDerivesPermutation normal
                (wordOfCons x
                  (x :: x :: x :: x ::
                    (((((z :: zs).erase x).erase x).erase x).erase x).erase x))
                hperm
            have withPrefix :=
              Derives.prepend (Word.singleton x) reorder
            cases he : (((((z :: zs).erase x).erase x).erase x).erase x).erase x with
            | nil =>
                have reduced :
                    senaryReduce (x :: y :: ys) = [] := by
                  change
                    (if (senaryReduce (y :: ys)).count x < 5 then
                      x :: senaryReduce (y :: ys)
                    else
                      (((((senaryReduce (y :: ys)).erase x).erase x).erase x).erase x).erase x) =
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
                  cyclicSixDerivesCancelSixth
                    (Word.singleton x) remainder
                have reduced :
                    senaryReduce (x :: y :: ys) = r :: rs := by
                  change
                    (if (senaryReduce (y :: ys)).count x < 5 then
                      x :: senaryReduce (y :: ys)
                    else
                      (((((senaryReduce (y :: ys)).erase x).erase x).erase x).erase x).erase x) =
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

theorem cyclicSixDerivesNormal (w : Word Nat) :
    match senaryReduce w.toList with
    | [] =>
        Derives basis w
          (((((Word.singleton w.head ++ Word.singleton w.head) ++
              Word.singleton w.head) ++ Word.singleton w.head) ++
            Word.singleton w.head) ++ Word.singleton w.head)
    | x :: xs =>
        Derives basis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact cyclicSixDerivesNormalizeList head tail

private def senaryValue (n : Nat) : Fin 6 :=
  cyclicSixEncode ⟨n % 6, Nat.mod_lt _ (by decide)⟩

private theorem cyclicSixMul_encode (a b : Fin 6) :
    cyclicSixMul (cyclicSixEncode a) (cyclicSixEncode b) =
      cyclicSixEncode ⟨(a.val + b.val) % 6, Nat.mod_lt _ (by decide)⟩ := by
  decide +revert

private theorem cyclicSixMul_senaryValue (m n : Nat) :
    cyclicSixMul (senaryValue m) (senaryValue n) =
      senaryValue (m + n) := by
  unfold senaryValue
  rw [cyclicSixMul_encode]
  apply congrArg cyclicSixEncode
  apply Fin.ext
  simp [Nat.add_mod]

private def senarySeparator (z : Nat) : Nat → Fin 6 :=
  fun x => if x = z then 5 else 0

private theorem cyclicSixFold_separator
    (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x =>
          cyclicSixMul current (senarySeparator z x))
        (senaryValue acc) =
      senaryValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show senarySeparator z z = senaryValue 1 by
          simp [senarySeparator, senaryValue,
            cyclicSixEncode]]
        rw [cyclicSixMul_senaryValue, ih]
        unfold senaryValue
        apply congrArg cyclicSixEncode
        apply Fin.ext
        simp [Nat.add_left_comm, Nat.add_comm]
      · rw [List.count_cons_of_ne hx]
        rw [show senarySeparator z x = senaryValue 0 by
          simp [senarySeparator, hx, senaryValue,
            cyclicSixEncode]]
        rw [cyclicSixMul_senaryValue, ih]
        unfold senaryValue
        apply congrArg cyclicSixEncode
        apply Fin.ext
        simp

theorem cyclicSixEval_separator (z : Nat) (w : Word Nat) :
    table.semigroup.eval (senarySeparator z) w =
      senaryValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              cyclicSixMul current (senarySeparator z x))
            (senarySeparator z head) =
          senaryValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show senarySeparator z z = senaryValue 1 by
          simp [senarySeparator, senaryValue,
            cyclicSixEncode]]
        rw [cyclicSixFold_separator]
        unfold senaryValue
        apply congrArg cyclicSixEncode
        apply Fin.ext
        simp [Nat.add_comm]
      · rw [List.count_cons_of_ne hhead]
        rw [show senarySeparator z head = senaryValue 0 by
          simp [senarySeparator, hhead, senaryValue,
            cyclicSixEncode]]
        rw [cyclicSixFold_separator]
        unfold senaryValue
        apply congrArg cyclicSixEncode
        apply Fin.ext
        simp

theorem cyclicSixValid_mod_eq (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ z, identity.lhs.toList.count z % 6 =
      identity.rhs.toList.count z % 6 := by
  intro z
  have evaluated := valid (senarySeparator z)
  rw [cyclicSixEval_separator, cyclicSixEval_separator] at evaluated
  have decoded := congrArg cyclicSixDecode evaluated
  simp only [senaryValue, cyclicSixDecode_encode] at decoded
  exact Fin.mk.inj decoded

/-- Unrestricted completeness over `Nat` variables.  Equal exponent vectors
modulo six normalize to the same zero-to-five-copy support; the zero vector
uses the common sixth-power class. -/
theorem basis_complete : BasisFor table.semigroup basis := by
  refine ⟨basis_models, ?_⟩
  intro identity valid
  have modEq := cyclicSixValid_mod_eq identity valid
  have reducedPerm :
      (senaryReduce identity.lhs.toList).Perm
        (senaryReduce identity.rhs.toList) :=
    senaryReduce_perm_of_mod_eq modEq
  have lhsNormal := cyclicSixDerivesNormal identity.lhs
  have rhsNormal := cyclicSixDerivesNormal identity.rhs
  cases hl : senaryReduce identity.lhs.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : senaryReduce identity.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicSixDerivesCommonSixth
            (Word.singleton identity.lhs.head)
            (Word.singleton identity.rhs.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : senaryReduce identity.rhs.toList with
      | nil =>
          rw [hl, hr] at reducedPerm
          exact False.elim (List.not_perm_cons_nil reducedPerm)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          rw [hl, hr] at reducedPerm
          exact Derives.trans lhsNormal <|
            Derives.trans
              (cyclicSixDerivesPermutation
                (wordOfCons x xs) (wordOfCons y ys) reducedPerm)
              (Derives.symm rhsNormal)

theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  basis_complete.oppositeReversed

end SemigroupBasis.CoRoots.Order6CyclicSix

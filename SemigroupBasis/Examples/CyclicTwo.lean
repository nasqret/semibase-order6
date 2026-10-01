import SemigroupBasis.FiniteTable

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Addition modulo two, presented as the exact table `[[1,2],[2,1]]`. -/
def cyclicTwoMul (a b : Fin 2) : Fin 2 :=
  ⟨(a.val + b.val) % 2, Nat.mod_lt _ (by decide)⟩

/-- The cyclic group of order two, viewed only as a semigroup. -/
def cyclicTwo : FiniteTable where
  order := 2
  mul := cyclicTwoMul
  assoc := by decide

def cyclicX : Word Nat := Word.singleton 0
def cyclicY : Word Nat := Word.singleton 1
def cyclicXY : Word Nat := ⟨0, [1]⟩
def cyclicYX : Word Nat := ⟨1, [0]⟩
def cyclicXXY : Word Nat := ⟨0, [0, 1]⟩

def cyclicCommutativityLaw : Identity Nat :=
  ⟨cyclicXY, cyclicYX⟩

def cyclicCancellationLaw : Identity Nat :=
  ⟨cyclicXXY, cyclicY⟩

/-- The classical semigroup basis `xy = yx`, `xxy = y`. -/
def cyclicTwoBasis : List (Identity Nat) :=
  [cyclicCommutativityLaw, cyclicCancellationLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem cyclicDerivesCommutativity (u v : Word Nat) :
    Derives cyclicTwoBasis (u ++ v) (v ++ u) := by
  have hbase :
      Derives cyclicTwoBasis cyclicXY cyclicYX :=
    Derives.fromBasis (e := cyclicCommutativityLaw) <| by
      exact List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [cyclicTwoBasis, cyclicCommutativityLaw, cyclicXY, cyclicYX,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton] using h

theorem cyclicDerivesCancelSquare (u v : Word Nat) :
    Derives cyclicTwoBasis ((u ++ u) ++ v) v := by
  have hbase :
      Derives cyclicTwoBasis cyclicXXY cyclicY :=
    Derives.fromBasis (e := cyclicCancellationLaw) <| by
      exact List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [cyclicTwoBasis, cyclicCancellationLaw, cyclicXXY, cyclicY,
    instantiateTwoWords, Word.bind, Word.append, Word.singleton,
    Word.append_assoc] using h

theorem cyclicDerivesTriple (u : Word Nat) :
    Derives cyclicTwoBasis ((u ++ u) ++ u) u :=
  cyclicDerivesCancelSquare u u

/-- Every square represents the unique nonempty all-even normal form. -/
theorem cyclicDerivesCommonSquare (u v : Word Nat) :
    Derives cyclicTwoBasis (u ++ u) (v ++ v) := by
  have addV :
      Derives cyclicTwoBasis (u ++ u) ((v ++ v) ++ (u ++ u)) :=
    Derives.symm (cyclicDerivesCancelSquare v (u ++ u))
  have commute :
      Derives cyclicTwoBasis ((v ++ v) ++ (u ++ u))
        ((u ++ u) ++ (v ++ v)) :=
    cyclicDerivesCommutativity (v ++ v) (u ++ u)
  exact Derives.trans addV <|
    Derives.trans commute (cyclicDerivesCancelSquare u (v ++ v))

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

private inductive ListDerives : List Nat → List Nat → Prop
  | empty : ListDerives [] []
  | words {x y : Nat} {xs ys : List Nat} :
      Derives cyclicTwoBasis (wordOfCons x xs) (wordOfCons y ys) →
        ListDerives (x :: xs) (y :: ys)

private theorem listDerives_of_perm {xs ys : List Nat}
    (h : xs.Perm ys) : ListDerives xs ys := by
  induction h with
  | nil =>
      exact ListDerives.empty
  | cons x h ih =>
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
              cyclicDerivesCommutativity
                (Word.singleton y) (Word.singleton x)
        | cons z zs =>
            have swapped :=
              Derives.appendRight
                (cyclicDerivesCommutativity
                  (Word.singleton y) (Word.singleton x))
                (wordOfCons z zs)
            simpa [wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using swapped
  | trans h₁ h₂ ih₁ ih₂ =>
      cases ih₁ with
      | empty =>
          cases ih₂
          exact ListDerives.empty
      | words first =>
          cases ih₂ with
          | words second =>
              exact ListDerives.words (Derives.trans first second)

theorem cyclicDerivesPermutation (u v : Word Nat)
    (h : u.toList.Perm v.toList) :
    Derives cyclicTwoBasis u v := by
  cases u with
      | mk uHead uTail =>
      cases v with
      | mk vHead vTail =>
          cases listDerives_of_perm h with
          | words derivation =>
              exact derivation

/-- Toggle membership. The result is a duplicate-free representative of the
parity vector of the input list. -/
def parityReduce : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let reduced := parityReduce xs
      if x ∈ reduced then reduced.erase x else x :: reduced

theorem parityReduce_nodup (xs : List Nat) :
    (parityReduce xs).Nodup := by
  induction xs with
  | nil =>
      exact List.nodup_nil
  | cons x xs ih =>
      simp only [parityReduce]
      split
      · exact ih.erase x
      · exact List.nodup_cons.2 ⟨by assumption, ih⟩

theorem mem_parityReduce_iff (z : Nat) (xs : List Nat) :
    z ∈ parityReduce xs ↔ xs.count z % 2 = 1 := by
  induction xs with
  | nil =>
      simp [parityReduce]
  | cons x xs ih =>
      simp only [parityReduce]
      by_cases hx : x ∈ parityReduce xs
      · simp only [hx, if_pos]
        by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self]
          have hodd : xs.count x % 2 = 1 := ih.mp hx
          simp [(parityReduce_nodup xs).mem_erase_iff, hodd,
            Nat.add_mod]
        · rw [List.mem_erase_of_ne hzx]
          rw [List.count_cons_of_ne (Ne.symm hzx)]
          exact ih
      · rw [if_neg hx]
        rw [List.mem_cons]
        by_cases hzx : z = x
        · subst z
          rw [List.count_cons_self]
          have heven : xs.count x % 2 = 0 := by
            have hne : xs.count x % 2 ≠ 1 := fun h => hx (ih.mpr h)
            omega
          simp [Nat.add_mod, heven]
        · rw [List.count_cons_of_ne (Ne.symm hzx)]
          simp [hzx, ih]

theorem parityReduce_perm_of_parity_eq {xs ys : List Nat}
    (hparity : ∀ z, xs.count z % 2 = ys.count z % 2) :
    (parityReduce xs).Perm (parityReduce ys) := by
  rw [List.perm_iff_count]
  intro z
  have leftNodup := parityReduce_nodup xs
  have rightNodup := parityReduce_nodup ys
  rw [leftNodup.count, rightNodup.count]
  have hmem :
      z ∈ parityReduce xs ↔ z ∈ parityReduce ys := by
    rw [mem_parityReduce_iff, mem_parityReduce_iff, hparity z]
  simp only [hmem]

private theorem erase_eq_nil_of_mem {x : Nat} {xs : List Nat}
    (hx : x ∈ xs) (hempty : xs.erase x = []) :
    xs = [x] := by
  have hperm := List.perm_cons_erase hx
  rw [hempty] at hperm
  exact hperm.eq_singleton

private theorem cyclicDerivesNormalizeList :
    ∀ x xs,
      match parityReduce (x :: xs) with
      | [] =>
          Derives cyclicTwoBasis (wordOfCons x xs)
            (Word.singleton x ++ Word.singleton x)
      | y :: ys =>
          Derives cyclicTwoBasis (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := cyclicDerivesNormalizeList y ys
      cases hs : parityReduce (y :: ys) with
      | nil =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have squares :=
            Derives.prepend (Word.singleton x) <|
              cyclicDerivesCommonSquare
                (Word.singleton y) (Word.singleton x)
          have reduced : parityReduce (x :: y :: ys) = [x] := by
            change
              (if x ∈ parityReduce (y :: ys) then
                (parityReduce (y :: ys)).erase x
              else x :: parityReduce (y :: ys)) = [x]
            rw [hs]
            rfl
          rw [reduced]
          exact Derives.trans
            (by
              simpa [wordOfCons, Word.append, Word.singleton,
                Word.append_assoc] using prefixed)
            (Derives.trans
              (by
                simpa [Word.append_assoc] using squares)
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using
                    cyclicDerivesTriple (Word.singleton x)))
      | cons z zs =>
          rw [hs] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          let normal : Word Nat := wordOfCons z zs
          by_cases hx : x ∈ z :: zs
          · have hperm :
                (z :: zs).Perm (x :: (z :: zs).erase x) :=
              List.perm_cons_erase hx
            have reorder :
                Derives cyclicTwoBasis normal
                  (wordOfCons x ((z :: zs).erase x)) :=
              cyclicDerivesPermutation normal
                (wordOfCons x ((z :: zs).erase x)) hperm
            have withPrefix :=
              Derives.prepend (Word.singleton x) reorder
            cases he : (z :: zs).erase x with
            | nil =>
                rw [he] at withPrefix
                have singleton :
                    z :: zs = [x] :=
                  erase_eq_nil_of_mem hx he
                have reduced :
                    parityReduce (x :: y :: ys) = [] := by
                  change
                    (if x ∈ parityReduce (y :: ys) then
                      (parityReduce (y :: ys)).erase x
                    else x :: parityReduce (y :: ys)) = []
                  rw [hs, if_pos hx, he]
                rw [reduced]
                exact Derives.trans
                  (by
                    simpa [normal, wordOfCons, Word.append, Word.singleton,
                      Word.append_assoc] using prefixed)
                  (by
                    simpa [normal, wordOfCons, singleton, Word.append,
                      Word.singleton, Word.append_assoc] using withPrefix)
            | cons r rs =>
                rw [he] at withPrefix
                let remainder : Word Nat := wordOfCons r rs
                have cancel :=
                  cyclicDerivesCancelSquare (Word.singleton x) remainder
                have reduced :
                    parityReduce (x :: y :: ys) = r :: rs := by
                  change
                    (if x ∈ parityReduce (y :: ys) then
                      (parityReduce (y :: ys)).erase x
                    else x :: parityReduce (y :: ys)) = r :: rs
                  rw [hs, if_pos hx, he]
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
          · have reduced :
                parityReduce (x :: y :: ys) = x :: z :: zs := by
              change
                (if x ∈ parityReduce (y :: ys) then
                  (parityReduce (y :: ys)).erase x
                else x :: parityReduce (y :: ys)) = x :: z :: zs
              rw [hs, if_neg hx]
            rw [reduced]
            simpa [normal, wordOfCons, Word.append, Word.singleton,
              Word.append_assoc] using prefixed
termination_by
  _ xs => xs.length

theorem cyclicDerivesNormal (w : Word Nat) :
    match parityReduce w.toList with
    | [] =>
        Derives cyclicTwoBasis w
          (Word.singleton w.head ++ Word.singleton w.head)
    | x :: xs =>
        Derives cyclicTwoBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact cyclicDerivesNormalizeList head tail

private def parityValue (n : Nat) : Fin 2 :=
  ⟨n % 2, Nat.mod_lt _ (by decide)⟩

private theorem cyclicMul_parityValue (m n : Nat) :
    cyclicTwoMul (parityValue m) (parityValue n) =
      parityValue (m + n) := by
  apply Fin.ext
  simp [cyclicTwoMul, parityValue, Nat.add_mod]

private def paritySeparator (z : Nat) : Nat → Fin 2 :=
  fun x => if x = z then 1 else 0

private theorem cyclicFold_separator (z : Nat) (xs : List Nat) (acc : Nat) :
    xs.foldl
        (fun current x => cyclicTwoMul current (paritySeparator z x))
        (parityValue acc) =
      parityValue (acc + xs.count z) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x = z
      · subst x
        rw [List.count_cons_self]
        rw [show paritySeparator z z = parityValue 1 by
          simp [paritySeparator, parityValue]]
        rw [cyclicMul_parityValue, ih]
        apply Fin.ext
        simp [parityValue, Nat.add_comm, Nat.add_left_comm]
      · rw [List.count_cons_of_ne hx]
        rw [show paritySeparator z x = parityValue 0 by
          simp [paritySeparator, hx, parityValue]]
        rw [cyclicMul_parityValue, ih]
        apply Fin.ext
        simp [parityValue]

theorem cyclicEval_separator (z : Nat) (w : Word Nat) :
    cyclicTwo.semigroup.eval (paritySeparator z) w =
      parityValue (w.toList.count z) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x => cyclicTwoMul current (paritySeparator z x))
            (paritySeparator z head) =
          parityValue ((head :: tail).count z)
      by_cases hhead : head = z
      · subst head
        rw [List.count_cons_self]
        rw [show paritySeparator z z = parityValue 1 by
          simp [paritySeparator, parityValue]]
        rw [cyclicFold_separator]
        apply Fin.ext
        simp [parityValue, Nat.add_comm]
      · rw [List.count_cons_of_ne hhead]
        rw [show paritySeparator z head = parityValue 0 by
          simp [paritySeparator, hhead, parityValue]]
        rw [cyclicFold_separator]
        apply Fin.ext
        simp [parityValue]

theorem cyclicValid_parity_eq (e : Identity Nat)
    (valid : e.SatisfiedBy cyclicTwo.semigroup) :
    ∀ z, e.lhs.toList.count z % 2 = e.rhs.toList.count z % 2 := by
  intro z
  have evaluated := valid (paritySeparator z)
  rw [cyclicEval_separator, cyclicEval_separator] at evaluated
  exact Fin.mk.inj evaluated

theorem cyclicTwoBasis_models :
    Models cyclicTwo.semigroup cyclicTwoBasis := by
  intro e he
  simp only [cyclicTwoBasis, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change cyclicTwoMul (valuation 0) (valuation 1) =
      cyclicTwoMul (valuation 1) (valuation 0)
    apply Fin.ext
    simp [cyclicTwoMul, Nat.add_comm]
  · intro valuation
    change
      cyclicTwoMul (cyclicTwoMul (valuation 0) (valuation 0))
          (valuation 1) =
        valuation 1
    have cancellation (a b : Fin 2) :
        cyclicTwoMul (cyclicTwoMul a a) b = b := by
      decide +revert
    exact cancellation (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables. Distinct parity vectors
are separated by a one-variable valuation; equal vectors normalize to the same
duplicate-free odd support, while the zero vector uses a common square. -/
theorem cyclicTwoBasis_complete :
    BasisFor cyclicTwo.semigroup cyclicTwoBasis := by
  refine ⟨cyclicTwoBasis_models, ?_⟩
  intro e valid
  have parityEq := cyclicValid_parity_eq e valid
  have reducedPerm :
      (parityReduce e.lhs.toList).Perm
        (parityReduce e.rhs.toList) :=
    parityReduce_perm_of_parity_eq parityEq
  have lhsNormal := cyclicDerivesNormal e.lhs
  have rhsNormal := cyclicDerivesNormal e.rhs
  cases hl : parityReduce e.lhs.toList with
  | nil =>
      rw [hl] at reducedPerm
      have hr : parityReduce e.rhs.toList = [] :=
        reducedPerm.nil_eq.symm
      rw [hl] at lhsNormal
      rw [hr] at rhsNormal
      exact Derives.trans lhsNormal <|
        Derives.trans
          (cyclicDerivesCommonSquare
            (Word.singleton e.lhs.head)
            (Word.singleton e.rhs.head))
          (Derives.symm rhsNormal)
  | cons x xs =>
      cases hr : parityReduce e.rhs.toList with
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

end SemigroupBasis.Examples

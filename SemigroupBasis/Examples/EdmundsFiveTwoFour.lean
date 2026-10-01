import SemigroupBasis.FiniteTable
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Multiplication for the zero-based form of Edmunds' `S(5,2)`,
`[[1,1,1,1],[1,1,1,2],[3,3,3,3],[1,2,3,4]]`. -/
def edmundsFiveTwoFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 1 then (if b = 3 then 1 else 0) else
      if a = 2 then 2 else b

/-- The exact four-element Smallsemi representative `S4_75`. -/
def edmundsFiveTwoFour : FiniteTable where
  order := 4
  mul := edmundsFiveTwoFourMul
  assoc := by decide

def edmundsX : Word Nat := Word.singleton 0
def edmundsXX : Word Nat := ⟨0, [0]⟩
def edmundsXXX : Word Nat := ⟨0, [0, 0]⟩
def edmundsXYX : Word Nat := ⟨0, [1, 0]⟩
def edmundsXXY : Word Nat := ⟨0, [0, 1]⟩

def edmundsPowerLaw : Identity Nat :=
  ⟨edmundsXX, edmundsXXX⟩

def edmundsGatherLaw : Identity Nat :=
  ⟨edmundsXYX, edmundsXXY⟩

/-- Edmunds' basis for `S(5,2)`: `xx = xxx`, `xyx = xxy`. -/
def edmundsFiveTwoFourBasis : List (Identity Nat) :=
  [edmundsPowerLaw, edmundsGatherLaw]

private def instantiateTwoWords (u v : Word Nat) : Nat → Word Nat
  | 0 => u
  | 1 => v
  | n + 2 => Word.singleton (n + 2)

theorem edmundsDerivesPowerContraction (u : Word Nat) :
    Derives edmundsFiveTwoFourBasis ((u ++ u) ++ u) (u ++ u) := by
  have hbase :
      Derives edmundsFiveTwoFourBasis edmundsXXX edmundsXX :=
    Derives.symm <|
      Derives.fromBasis (e := edmundsPowerLaw) <| List.Mem.head _
  have h := Derives.subst hbase (instantiateTwoWords u u)
  simpa [edmundsFiveTwoFourBasis, edmundsPowerLaw, edmundsXXX,
    edmundsXX, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

theorem edmundsDerivesGather (u v : Word Nat) :
    Derives edmundsFiveTwoFourBasis
      ((u ++ v) ++ u) ((u ++ u) ++ v) := by
  have hbase :
      Derives edmundsFiveTwoFourBasis edmundsXYX edmundsXXY :=
    Derives.fromBasis (e := edmundsGatherLaw) <|
      List.Mem.tail _ (List.Mem.head _)
  have h := Derives.subst hbase (instantiateTwoWords u v)
  simpa [edmundsFiveTwoFourBasis, edmundsGatherLaw, edmundsXYX,
    edmundsXXY, instantiateTwoWords, Word.bind, Word.append,
    Word.singleton, Word.append_assoc] using h

private def wordOfCons (x : Nat) (xs : List Nat) : Word Nat :=
  ⟨x, xs⟩

/-- Move one later occurrence of the initial letter next to the initial
letter, preserving the intervening block and suffix. -/
private theorem edmundsDerivesFirstRepeat
    (x : Nat) (middle suffix : List Nat) :
    Derives edmundsFiveTwoFourBasis
      (wordOfCons x (middle ++ x :: suffix))
      (wordOfCons x (x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      exact Derives.refl _
  | cons y ys =>
      let middleWord := wordOfCons y ys
      cases suffix with
      | nil =>
          simpa [wordOfCons, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using
              edmundsDerivesGather (Word.singleton x) middleWord
      | cons z zs =>
          have h :=
            Derives.appendRight
              (edmundsDerivesGather (Word.singleton x) middleWord)
              (wordOfCons z zs)
          simpa [wordOfCons, middleWord, Word.append, Word.singleton,
            Word.append_assoc] using h

/-- Once two initial copies have been gathered, delete one additional later
copy by gathering it into a triple and contracting the triple. -/
private theorem edmundsDerivesDeleteExtra
    (x : Nat) (middle suffix : List Nat) :
    Derives edmundsFiveTwoFourBasis
      (wordOfCons x (x :: middle ++ x :: suffix))
      (wordOfCons x (x :: middle ++ suffix)) := by
  cases middle with
  | nil =>
      cases suffix with
      | nil =>
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using
              edmundsDerivesPowerContraction (Word.singleton x)
      | cons z zs =>
          have h :=
            Derives.appendRight
              (edmundsDerivesPowerContraction (Word.singleton x))
              (wordOfCons z zs)
          simpa [wordOfCons, Word.append, Word.singleton,
            Word.append_assoc] using h
  | cons y ys =>
      let middleWord := wordOfCons y ys
      have move :=
        Derives.prepend (Word.singleton x) <|
          edmundsDerivesGather (Word.singleton x) middleWord
      have contract :=
        Derives.appendRight
          (edmundsDerivesPowerContraction (Word.singleton x))
          middleWord
      cases suffix with
      | nil =>
          exact Derives.trans
            (by
              simpa [wordOfCons, middleWord, Word.append, Word.singleton,
                Word.append_assoc] using move)
            (by
              simpa [wordOfCons, middleWord, Word.append, Word.singleton,
                Word.append_assoc] using contract)
      | cons z zs =>
          have moveWithSuffix :=
            Derives.appendRight move (wordOfCons z zs)
          have contractWithSuffix :=
            Derives.appendRight contract (wordOfCons z zs)
          exact Derives.trans
            (by
              simpa [wordOfCons, middleWord, Word.append, Word.singleton,
                Word.append_assoc] using moveWithSuffix)
            (by
              simpa [wordOfCons, middleWord, Word.append, Word.singleton,
                Word.append_assoc] using contractWithSuffix)

/-- Delete all additional occurrences of `x` after an already gathered
initial square. -/
private theorem edmundsDerivesDeleteExtras :
    ∀ (x : Nat) (middle rest : List Nat),
      Derives edmundsFiveTwoFourBasis
        (wordOfCons x (x :: middle ++ rest))
        (wordOfCons x
          (x :: middle ++ rest.filter (fun y => decide (y ≠ x))))
  | x, middle, [] => by
      simpa using Derives.refl (wordOfCons x (x :: middle))
  | x, middle, y :: ys => by
      by_cases hy : y = x
      · subst y
        exact Derives.trans
          (edmundsDerivesDeleteExtra x middle ys) <| by
            simpa using edmundsDerivesDeleteExtras x middle ys
      · have remaining :=
          edmundsDerivesDeleteExtras x (middle ++ [y]) ys
        simpa [hy, List.append_assoc] using remaining

/-- Gather every occurrence of `x` after the initial one. If there is a
repeat, exactly two initial copies remain; otherwise the word is unchanged. -/
private theorem edmundsDerivesGatherInitial :
    ∀ (x : Nat) (middle rest : List Nat),
      Derives edmundsFiveTwoFourBasis
        (wordOfCons x (middle ++ rest))
        (if x ∈ rest then
          wordOfCons x
            (x :: middle ++ rest.filter (fun y => decide (y ≠ x)))
        else
          wordOfCons x (middle ++ rest))
  | x, middle, [] => by
      simpa using Derives.refl (wordOfCons x middle)
  | x, middle, y :: ys => by
      by_cases hy : y = x
      · subst y
        simp only [List.mem_cons, true_or, if_true]
        exact Derives.trans
          (edmundsDerivesFirstRepeat x middle ys) <| by
            simpa using edmundsDerivesDeleteExtras x middle ys
      · have remaining :=
          edmundsDerivesGatherInitial x (middle ++ [y]) ys
        have hxy : x ≠ y := Ne.symm hy
        by_cases hx : x ∈ ys
        · simpa [hy, hxy, hx, List.append_assoc] using remaining
        · simpa [hy, hxy, hx, List.append_assoc] using remaining

/-- The global normal form: variables occur in first-occurrence order, and
each first-occurrence block has length one or two according as the variable
occurs once or more than once. -/
def edmundsNormalList : List Nat → List Nat
  | [] => []
  | x :: xs =>
      let rest := edmundsNormalList xs
      if x ∈ rest then
        x :: x :: rest.filter (fun y => decide (y ≠ x))
      else
        x :: rest

private theorem edmundsNormalList_cons_ne_nil (x : Nat) (xs : List Nat) :
    edmundsNormalList (x :: xs) ≠ [] := by
  simp only [edmundsNormalList]
  split <;> simp

theorem edmundsNormalList_mem (z : Nat) :
    ∀ xs : List Nat, z ∈ edmundsNormalList xs ↔ z ∈ xs
  | [] => by simp [edmundsNormalList]
  | x :: xs => by
      simp only [edmundsNormalList]
      by_cases hx : x ∈ edmundsNormalList xs
      · by_cases hzx : z = x <;>
          simp [hx, hzx, edmundsNormalList_mem z xs]
      · simp [hx, edmundsNormalList_mem z xs]

/-- Every nonempty word derives to the unrestricted global normal form. -/
private theorem edmundsDerivesNormalizeList :
    ∀ x xs,
      match edmundsNormalList (x :: xs) with
      | [] => False
      | y :: ys =>
          Derives edmundsFiveTwoFourBasis
            (wordOfCons x xs) (wordOfCons y ys)
  | x, [] => by
      exact Derives.refl _
  | x, y :: ys => by
      have suffixNormal := edmundsDerivesNormalizeList y ys
      cases hn : edmundsNormalList (y :: ys) with
      | nil =>
          exact False.elim <|
            edmundsNormalList_cons_ne_nil y ys hn
      | cons z zs =>
          rw [hn] at suffixNormal
          have prefixed :=
            Derives.prepend (Word.singleton x) suffixNormal
          have gathered :=
            edmundsDerivesGatherInitial x [] (z :: zs)
          by_cases hx : x ∈ z :: zs
          · rw [if_pos hx] at gathered
            have normalEq :
                edmundsNormalList (x :: y :: ys) =
                  x :: x ::
                    (z :: zs).filter (fun a => decide (a ≠ x)) := by
              change
                (let rest := edmundsNormalList (y :: ys)
                 if x ∈ rest then
                   x :: x :: rest.filter (fun a => decide (a ≠ x))
                 else x :: rest) =
                  x :: x ::
                    (z :: zs).filter (fun a => decide (a ≠ x))
              rw [hn]
              simp [hx]
            rw [normalEq]
            exact Derives.trans
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using prefixed)
              (by
                simpa [edmundsNormalList, hn, hx, wordOfCons] using
                  gathered)
          · rw [if_neg hx] at gathered
            have normalEq :
                edmundsNormalList (x :: y :: ys) = x :: z :: zs := by
              change
                (let rest := edmundsNormalList (y :: ys)
                 if x ∈ rest then
                   x :: x :: rest.filter (fun a => decide (a ≠ x))
                 else x :: rest) = x :: z :: zs
              rw [hn]
              simp [hx]
            rw [normalEq]
            exact Derives.trans
              (by
                simpa [wordOfCons, Word.append, Word.singleton,
                  Word.append_assoc] using prefixed)
              (by
                simpa [edmundsNormalList, hn, hx, wordOfCons] using
                  gathered)

theorem edmundsDerivesNormal (w : Word Nat) :
    match edmundsNormalList w.toList with
    | [] => False
    | x :: xs =>
        Derives edmundsFiveTwoFourBasis w (wordOfCons x xs) := by
  cases w with
  | mk head tail =>
      exact edmundsDerivesNormalizeList head tail

/-- Lists in block normal form. Each variable has one block, of length one
or two, and never occurs in a later block. -/
private inductive EdmundsNormal : List Nat → Prop
  | nil : EdmundsNormal []
  | single (x : Nat) (xs : List Nat) :
      EdmundsNormal xs → x ∉ xs → EdmundsNormal (x :: xs)
  | double (x : Nat) (xs : List Nat) :
      EdmundsNormal xs → x ∉ xs → EdmundsNormal (x :: x :: xs)

private theorem EdmundsNormal.filter_ne
    {xs : List Nat} (normal : EdmundsNormal xs) (x : Nat) :
    EdmundsNormal (xs.filter (fun y => decide (y ≠ x))) := by
  induction normal with
  | nil =>
      exact EdmundsNormal.nil
  | single y ys normalY yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have wholeFilterEq :
            (x :: ys).filter (fun z => decide (z ≠ x)) = ys := by
          have tailFilterEq :
              ys.filter (fun z => decide (z ≠ x)) = ys := by
            apply List.filter_eq_self.mpr
            intro z hz
            have hzx : z ≠ x := by
              intro h
              subst z
              exact yNotMem hz
            simp [hzx]
          rw [List.filter_cons_of_neg (by simp)]
          exact tailFilterEq
        rw [wholeFilterEq]
        exact normalY
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          simp only [List.mem_filter]
          exact fun h => yNotMem h.1
        simpa [hyx] using
          EdmundsNormal.single y
            (ys.filter (fun z => decide (z ≠ x))) ih yNotMemFilter
  | double y ys normalY yNotMem ih =>
      by_cases hyx : y = x
      · subst y
        have wholeFilterEq :
            (x :: x :: ys).filter (fun z => decide (z ≠ x)) = ys := by
          have tailFilterEq :
              ys.filter (fun z => decide (z ≠ x)) = ys := by
            apply List.filter_eq_self.mpr
            intro z hz
            have hzx : z ≠ x := by
              intro h
              subst z
              exact yNotMem hz
            simp [hzx]
          rw [List.filter_cons_of_neg (by simp),
            List.filter_cons_of_neg (by simp)]
          exact tailFilterEq
        rw [wholeFilterEq]
        exact normalY
      · have yNotMemFilter :
            y ∉ ys.filter (fun z => decide (z ≠ x)) := by
          simp only [List.mem_filter]
          exact fun h => yNotMem h.1
        simpa [hyx] using
          EdmundsNormal.double y
            (ys.filter (fun z => decide (z ≠ x))) ih yNotMemFilter

private theorem edmundsNormalList_normal :
    ∀ xs : List Nat, EdmundsNormal (edmundsNormalList xs)
  | [] => by
      exact EdmundsNormal.nil
  | x :: xs => by
      have restNormal := edmundsNormalList_normal xs
      by_cases hx : x ∈ edmundsNormalList xs
      · have filteredNormal := restNormal.filter_ne x
        have xNotMem :
            x ∉ (edmundsNormalList xs).filter
              (fun y => decide (y ≠ x)) := by
          simp
        simpa [edmundsNormalList, hx] using
          EdmundsNormal.double x
            ((edmundsNormalList xs).filter
              (fun y => decide (y ≠ x)))
            filteredNormal xNotMem
      · simpa [edmundsNormalList, hx] using
          EdmundsNormal.single x (edmundsNormalList xs) restNormal hx

/-- Evaluation of a possibly empty list, using the identity element `3`. -/
private def edmundsListEval
    (valuation : Nat → Fin 4) (xs : List Nat) : Fin 4 :=
  xs.foldl
    (fun current x => edmundsFiveTwoFourMul current (valuation x)) 3

private theorem edmundsMul_left_zero (b : Fin 4) :
    edmundsFiveTwoFourMul 0 b = 0 := by
  simp [edmundsFiveTwoFourMul]

private theorem edmundsMul_left_two (b : Fin 4) :
    edmundsFiveTwoFourMul 2 b = 2 := by
  simp [edmundsFiveTwoFourMul]

private theorem edmundsMul_left_identity (b : Fin 4) :
    edmundsFiveTwoFourMul 3 b = b := by
  simp [edmundsFiveTwoFourMul]

private theorem edmundsMul_right_identity (a : Fin 4) :
    edmundsFiveTwoFourMul a 3 = a := by
  decide +revert

private theorem edmundsFold_left_zero
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          edmundsFiveTwoFourMul current (valuation x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, edmundsMul_left_zero] using ih

private theorem edmundsFold_left_two
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          edmundsFiveTwoFourMul current (valuation x)) 2 = 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, edmundsMul_left_two] using ih

private theorem edmundsFold_all_three
    (valuation : Nat → Fin 4) :
    ∀ (xs : List Nat) (acc : Fin 4),
      (∀ z, z ∈ xs → valuation z = 3) →
      xs.foldl
          (fun current z =>
            edmundsFiveTwoFourMul current (valuation z)) acc = acc
  | [], _, _ => rfl
  | z :: zs, acc, hall => by
      simp only [List.foldl_cons]
      rw [hall z (List.Mem.head zs), edmundsMul_right_identity]
      exact edmundsFold_all_three valuation zs acc
        (fun y hy => hall y (List.Mem.tail z hy))

private theorem edmundsListEval_cons_zero
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 0) :
    edmundsListEval valuation (x :: xs) = 0 := by
  unfold edmundsListEval
  simp only [List.foldl_cons]
  rw [edmundsMul_left_identity, hx]
  exact edmundsFold_left_zero valuation xs

private theorem edmundsListEval_cons_two
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 2) :
    edmundsListEval valuation (x :: xs) = 2 := by
  unfold edmundsListEval
  simp only [List.foldl_cons]
  rw [edmundsMul_left_identity, hx]
  exact edmundsFold_left_two valuation xs

private theorem edmundsListEval_cons_three
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 3) :
    edmundsListEval valuation (x :: xs) =
      edmundsListEval valuation xs := by
  simp [edmundsListEval, hx, edmundsMul_left_identity]

private theorem edmundsListEval_single_one
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 1)
    (hrest : ∀ z, z ∈ xs → valuation z = 3) :
    edmundsListEval valuation (x :: xs) = 1 := by
  unfold edmundsListEval
  simp only [List.foldl_cons]
  rw [edmundsMul_left_identity, hx]
  exact edmundsFold_all_three valuation xs 1 hrest

private theorem edmundsListEval_double_one
    (valuation : Nat → Fin 4) (x : Nat) (xs : List Nat)
    (hx : valuation x = 1) :
    edmundsListEval valuation (x :: x :: xs) = 0 := by
  unfold edmundsListEval
  simp only [List.foldl_cons]
  rw [edmundsMul_left_identity, hx]
  change
    xs.foldl
        (fun current z =>
          edmundsFiveTwoFourMul current (valuation z))
        (edmundsFiveTwoFourMul 1 1) = 0
  have oneSquare :
      edmundsFiveTwoFourMul 1 1 = (0 : Fin 4) := by decide
  rw [oneSquare]
  exact edmundsFold_left_zero valuation xs

private theorem edmundsFold_congr
    (v₁ v₂ : Nat → Fin 4) :
    ∀ (xs : List Nat) (acc : Fin 4),
      (∀ x, x ∈ xs → v₁ x = v₂ x) →
      xs.foldl
          (fun current x =>
            edmundsFiveTwoFourMul current (v₁ x)) acc =
        xs.foldl
          (fun current x =>
            edmundsFiveTwoFourMul current (v₂ x)) acc
  | [], _, _ => rfl
  | x :: xs, acc, agree => by
      simp only [List.foldl_cons]
      rw [agree x (List.Mem.head xs)]
      exact edmundsFold_congr v₁ v₂ xs
        (edmundsFiveTwoFourMul acc (v₂ x))
        (fun y hy => agree y (List.Mem.tail x hy))

private theorem edmundsListEval_congr
    (v₁ v₂ : Nat → Fin 4) (xs : List Nat)
    (agree : ∀ x, x ∈ xs → v₁ x = v₂ x) :
    edmundsListEval v₁ xs = edmundsListEval v₂ xs :=
  edmundsFold_congr v₁ v₂ xs 3 agree

private theorem edmundsEval_eq_listEval
    (valuation : Nat → Fin 4) (w : Word Nat) :
    edmundsFiveTwoFour.semigroup.eval valuation w =
      edmundsListEval valuation w.toList := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              edmundsFiveTwoFourMul current (valuation x))
            (valuation head) =
          tail.foldl
            (fun current x =>
              edmundsFiveTwoFourMul current (valuation x))
            (edmundsFiveTwoFourMul 3 (valuation head))
      rw [edmundsMul_left_identity]

private theorem edmundsNormal_heads_eq
    (x y : Nat) (xs ys : List Nat)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        edmundsListEval valuation (x :: xs) =
          edmundsListEval valuation (y :: ys)) :
    x = y := by
  apply Decidable.byContradiction
  intro hxy
  let valuation : Nat → Fin 4 :=
    fun z => if z = x then 0 else if z = y then 2 else 3
  have h := equalEval valuation
  have leftValue :
      edmundsListEval valuation (x :: xs) = 0 :=
    edmundsListEval_cons_zero valuation x xs (by
      simp [valuation])
  have rightValue :
      edmundsListEval valuation (y :: ys) = 2 :=
    edmundsListEval_cons_two valuation y ys (by
      simp [valuation, Ne.symm hxy])
  rw [leftValue, rightValue] at h
  exact (by decide : (0 : Fin 4) ≠ 2) h

/-- Exact-table separators distinguish all global normal forms. -/
private theorem edmundsNormal_eq_of_eval_eq
    {xs ys : List Nat}
    (normalX : EdmundsNormal xs) (normalY : EdmundsNormal ys)
    (equalEval :
      ∀ valuation : Nat → Fin 4,
        edmundsListEval valuation xs =
          edmundsListEval valuation ys) :
    xs = ys := by
  induction normalX generalizing ys with
  | nil =>
      cases normalY with
      | nil => rfl
      | single y ys hy _ =>
          let valuation : Nat → Fin 4 :=
            fun z => if z = y then 0 else 3
          have h := equalEval valuation
          have rightValue :
              edmundsListEval valuation (y :: ys) = 0 :=
            edmundsListEval_cons_zero valuation y ys (by
              simp [valuation])
          change (3 : Fin 4) = edmundsListEval valuation (y :: ys) at h
          rw [rightValue] at h
          exact False.elim ((by decide : (3 : Fin 4) ≠ 0) h)
      | double y ys hy _ =>
          let valuation : Nat → Fin 4 :=
            fun z => if z = y then 0 else 3
          have h := equalEval valuation
          have rightValue :
              edmundsListEval valuation (y :: y :: ys) = 0 :=
            edmundsListEval_cons_zero valuation y (y :: ys) (by
              simp [valuation])
          change (3 : Fin 4) =
            edmundsListEval valuation (y :: y :: ys) at h
          rw [rightValue] at h
          exact False.elim ((by decide : (3 : Fin 4) ≠ 0) h)
  | single x xs normalTail xNotMem ih =>
      cases normalY with
      | nil =>
          let valuation : Nat → Fin 4 :=
            fun z => if z = x then 0 else 3
          have h := equalEval valuation
          have leftValue :
              edmundsListEval valuation (x :: xs) = 0 :=
            edmundsListEval_cons_zero valuation x xs (by
              simp [valuation])
          change edmundsListEval valuation (x :: xs) = (3 : Fin 4) at h
          rw [leftValue] at h
          exact False.elim ((by decide : (0 : Fin 4) ≠ 3) h)
      | single y ys normalRight yNotMem =>
          have heads : x = y :=
            edmundsNormal_heads_eq x y xs ys equalEval
          subst y
          have tailsEqual :
              ∀ valuation : Nat → Fin 4,
                edmundsListEval valuation xs =
                  edmundsListEval valuation ys := by
            intro valuation
            let masked : Nat → Fin 4 :=
              fun z => if z = x then 3 else valuation z
            have fullEqual := equalEval masked
            have maskedX : masked x = 3 := by simp [masked]
            rw [edmundsListEval_cons_three masked x xs maskedX,
              edmundsListEval_cons_three masked x ys maskedX] at fullEqual
            calc
              edmundsListEval valuation xs =
                  edmundsListEval masked xs := by
                    apply edmundsListEval_congr
                    intro z hz
                    have hzx : z ≠ x := by
                      intro h
                      apply xNotMem
                      simpa [h] using hz
                    simp [masked, hzx]
              _ = edmundsListEval masked ys := fullEqual
              _ = edmundsListEval valuation ys := by
                    apply edmundsListEval_congr
                    intro z hz
                    have hzx : z ≠ x := by
                      intro h
                      apply yNotMem
                      simpa [h] using hz
                    simp [masked, hzx]
          congr 1
          exact ih normalRight tailsEqual
      | double y ys normalRight yNotMem =>
          have heads : x = y :=
            edmundsNormal_heads_eq x y xs (y :: ys) equalEval
          subst y
          let valuation : Nat → Fin 4 :=
            fun z => if z = x then 1 else 3
          have h := equalEval valuation
          have leftValue :
              edmundsListEval valuation (x :: xs) = 1 :=
            edmundsListEval_single_one valuation x xs (by
              simp [valuation]) (by
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply xNotMem
                  simpa [h] using hz
                simp [valuation, hzx])
          have rightValue :
              edmundsListEval valuation (x :: x :: ys) = 0 :=
            edmundsListEval_double_one valuation x ys (by
              simp [valuation])
          rw [leftValue, rightValue] at h
          exact False.elim ((by decide : (1 : Fin 4) ≠ 0) h)
  | double x xs normalTail xNotMem ih =>
      cases normalY with
      | nil =>
          let valuation : Nat → Fin 4 :=
            fun z => if z = x then 0 else 3
          have h := equalEval valuation
          have leftValue :
              edmundsListEval valuation (x :: x :: xs) = 0 :=
            edmundsListEval_cons_zero valuation x (x :: xs) (by
              simp [valuation])
          change
            edmundsListEval valuation (x :: x :: xs) = (3 : Fin 4) at h
          rw [leftValue] at h
          exact False.elim ((by decide : (0 : Fin 4) ≠ 3) h)
      | single y ys normalRight yNotMem =>
          have heads : x = y :=
            edmundsNormal_heads_eq x y (x :: xs) ys equalEval
          subst y
          let valuation : Nat → Fin 4 :=
            fun z => if z = x then 1 else 3
          have h := equalEval valuation
          have leftValue :
              edmundsListEval valuation (x :: x :: xs) = 0 :=
            edmundsListEval_double_one valuation x xs (by
              simp [valuation])
          have rightValue :
              edmundsListEval valuation (x :: ys) = 1 :=
            edmundsListEval_single_one valuation x ys (by
              simp [valuation]) (by
                intro z hz
                have hzx : z ≠ x := by
                  intro h
                  apply yNotMem
                  simpa [h] using hz
                simp [valuation, hzx])
          rw [leftValue, rightValue] at h
          exact False.elim ((by decide : (0 : Fin 4) ≠ 1) h)
      | double y ys normalRight yNotMem =>
          have heads : x = y :=
            edmundsNormal_heads_eq x y (x :: xs) (y :: ys) equalEval
          subst y
          have tailsEqual :
              ∀ valuation : Nat → Fin 4,
                edmundsListEval valuation xs =
                  edmundsListEval valuation ys := by
            intro valuation
            let masked : Nat → Fin 4 :=
              fun z => if z = x then 3 else valuation z
            have fullEqual := equalEval masked
            have maskedX : masked x = 3 := by simp [masked]
            rw [edmundsListEval_cons_three masked x (x :: xs) maskedX,
              edmundsListEval_cons_three masked x xs maskedX,
              edmundsListEval_cons_three masked x (x :: ys) maskedX,
              edmundsListEval_cons_three masked x ys maskedX] at fullEqual
            calc
              edmundsListEval valuation xs =
                  edmundsListEval masked xs := by
                    apply edmundsListEval_congr
                    intro z hz
                    have hzx : z ≠ x := by
                      intro h
                      apply xNotMem
                      simpa [h] using hz
                    simp [masked, hzx]
              _ = edmundsListEval masked ys := fullEqual
              _ = edmundsListEval valuation ys := by
                    apply edmundsListEval_congr
                    intro z hz
                    have hzx : z ≠ x := by
                      intro h
                      apply yNotMem
                      simpa [h] using hz
                    simp [masked, hzx]
          congr 2
          exact ih normalRight tailsEqual

private theorem edmundsMul_power (a : Fin 4) :
    edmundsFiveTwoFourMul a a =
      edmundsFiveTwoFourMul
        (edmundsFiveTwoFourMul a a) a := by
  decide +revert

private theorem edmundsMul_gather (a b : Fin 4) :
    edmundsFiveTwoFourMul
        (edmundsFiveTwoFourMul a b) a =
      edmundsFiveTwoFourMul
        (edmundsFiveTwoFourMul a a) b := by
  decide +revert

theorem edmundsFiveTwoFourBasis_models :
    Models edmundsFiveTwoFour.semigroup
      edmundsFiveTwoFourBasis := by
  intro e he
  simp only [edmundsFiveTwoFourBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      edmundsFiveTwoFourMul (valuation 0) (valuation 0) =
        edmundsFiveTwoFourMul
          (edmundsFiveTwoFourMul (valuation 0) (valuation 0))
          (valuation 0)
    exact edmundsMul_power (valuation 0)
  · intro valuation
    change
      edmundsFiveTwoFourMul
          (edmundsFiveTwoFourMul (valuation 0) (valuation 1))
          (valuation 0) =
        edmundsFiveTwoFourMul
          (edmundsFiveTwoFourMul (valuation 0) (valuation 0))
          (valuation 1)
    exact edmundsMul_gather (valuation 0) (valuation 1)

/-- Unrestricted completeness over `Nat` variables. Every word derives to the
first-occurrence block normal form, and the exact four-element table separates
all distinct normal forms. -/
theorem edmundsFiveTwoFourBasis_complete :
    BasisFor edmundsFiveTwoFour.semigroup
      edmundsFiveTwoFourBasis := by
  refine ⟨edmundsFiveTwoFourBasis_models, ?_⟩
  intro e valid
  have lhsNormal := edmundsDerivesNormal e.lhs
  have rhsNormal := edmundsDerivesNormal e.rhs
  cases hl : edmundsNormalList e.lhs.toList with
  | nil =>
      exact False.elim <|
        edmundsNormalList_cons_ne_nil e.lhs.head e.lhs.tail (by
          simpa [Word.toList] using hl)
  | cons x xs =>
      cases hr : edmundsNormalList e.rhs.toList with
      | nil =>
          exact False.elim <|
            edmundsNormalList_cons_ne_nil e.rhs.head e.rhs.tail (by
              simpa [Word.toList] using hr)
      | cons y ys =>
          rw [hl] at lhsNormal
          rw [hr] at rhsNormal
          have reducedEvalEqual :
              ∀ valuation : Nat → Fin 4,
                edmundsListEval valuation (x :: xs) =
                  edmundsListEval valuation (y :: ys) := by
            intro valuation
            have lhsSound :=
              lhsNormal.sound edmundsFiveTwoFourBasis_models valuation
            have rhsSound :=
              rhsNormal.sound edmundsFiveTwoFourBasis_models valuation
            rw [edmundsEval_eq_listEval] at lhsSound rhsSound
            exact lhsSound.symm.trans ((valid valuation).trans rhsSound)
          have leftForm : EdmundsNormal (x :: xs) := by
            rw [← hl]
            exact edmundsNormalList_normal e.lhs.toList
          have rightForm : EdmundsNormal (y :: ys) := by
            rw [← hr]
            exact edmundsNormalList_normal e.rhs.toList
          have reducedEqual : x :: xs = y :: ys :=
            edmundsNormal_eq_of_eval_eq
              leftForm rightForm reducedEvalEqual
          cases reducedEqual
          exact Derives.trans lhsNormal (Derives.symm rhsNormal)

def edmundsFiveTwoFourOppositeBasis : List (Identity Nat) :=
  reversedBasis edmundsFiveTwoFourBasis

theorem edmundsFiveTwoFourOppositeBasis_complete :
    BasisFor edmundsFiveTwoFour.semigroup.opposite
      edmundsFiveTwoFourOppositeBasis := by
  simpa [edmundsFiveTwoFourOppositeBasis] using
    edmundsFiveTwoFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
